"""Incremental, pointwise interval Datalog engine.

Relations map tuples to sparse piecewise-constant *count functions* over
half-open integer time intervals.  A tuple exists at a time point exactly
when its count is positive.  Base changes are propagated incrementally,
semi-naive style: rules are only re-evaluated for derivations that touch a
changed tuple, and all arithmetic works on interval endpoints rather than on
individual integers (no per-integer expansion and no whole-relation
recomputation).

The language is function-free Datalog with conjunctive bodies and stratified
negation (``!``).  Positive recursion is allowed; a negation edge inside a
recursive component is rejected.
"""

import re
import sys

from . import segments as seg

_LITERAL_RE = re.compile(r"(!?)\s*([A-Za-z_]\w*)\s*\((.*)\)\s*$")


def _split_top_level(text):
    """Split a rule body on commas that are not inside parentheses."""
    parts, depth, start = [], 0, 0
    for i, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
    parts.append(text[start:])
    return parts


class Rule:
    __slots__ = ("head", "head_args", "body")

    def __init__(self, head, head_args, body):
        # body: list of (negated, name, args tuple)
        self.head = head
        self.head_args = head_args
        self.body = body

    def __repr__(self):
        parts = []
        for neg, name, args in self.body:
            parts.append(("!" if neg else "") + name + "(" + ",".join(args)
                         + ")")
        return "{}({}) :- {}".format(self.head, ",".join(self.head_args),
                                     ", ".join(parts))


class Engine:
    def __init__(self, base, rules):
        if not isinstance(base, dict) or not base:
            raise ValueError("base must be a non-empty name->arity mapping")
        self.base = {}
        for name, arity in base.items():
            if (not isinstance(name, str) or not name
                    or not isinstance(arity, int) or isinstance(arity, bool)
                    or arity < 0):
                raise ValueError("invalid base relation declaration: %r"
                                 % name)
            self.base[name] = arity
        self.rules = [self._parse_rule(r) for r in rules]
        self._validate()
        self._build_program()
        # relation -> tuple -> segment list (non-zero count function)
        self.store = {name: {} for name in self.all_arity}
        # relation -> column -> value -> set of tuples ever inserted
        self.indexes = {name: [dict() for _ in range(arity)]
                        for name, arity in self.all_arity.items()}

    # ------------------------------------------------------------------ parse
    def _parse_literal(self, text):
        m = _LITERAL_RE.match(text.strip())
        if not m:
            raise ValueError("cannot parse literal: %r" % text)
        neg = m.group(1) == "!"
        name = m.group(2)
        inside = m.group(3)
        args = tuple(a.strip() for a in inside.split(",")) \
            if inside.strip() else ()
        if any(not a for a in args):
            raise ValueError("empty argument in literal: %r" % text)
        for a in args:
            if not a.isidentifier() or not (a[0].isupper() or a[0] == "_"):
                raise ValueError("only variables are allowed, got: %r" % a)
        return neg, name, args

    def _parse_rule(self, text):
        if not isinstance(text, str) or ":-" not in text:
            raise ValueError("rule must contain ':-': %r" % text)
        head_txt, body_txt = text.split(":-", 1)
        hneg, hname, hargs = self._parse_literal(head_txt)
        if hneg:
            raise ValueError("rule head cannot be negated: %r" % text)
        if not body_txt.strip():
            raise ValueError("rule body is empty: %r" % text)
        body = [self._parse_literal(p) for p in _split_top_level(body_txt)]
        if not any(not neg for neg, _, _ in body):
            raise ValueError("rule %s needs at least one positive literal"
                             % hname)
        return Rule(hname, hargs, body)

    def _validate(self):
        idb_arity = {}
        for r in self.rules:
            if r.head in self.base:
                raise ValueError("base relation %s cannot be a rule head"
                                 % r.head)
            if r.head in idb_arity and idb_arity[r.head] != len(r.head_args):
                raise ValueError("arity conflict for derived relation %s"
                                 % r.head)
            idb_arity[r.head] = len(r.head_args)
            if len(set(r.head_args)) != len(r.head_args):
                raise ValueError("head variables must be distinct in %s" % r)
            pos_vars = set()
            for neg, name, args in r.body:
                if name in self.base:
                    arity = self.base[name]
                elif name in idb_arity:
                    arity = idb_arity[name]
                else:
                    raise ValueError("undefined relation %s in rule %s"
                                     % (name, r))
                if arity != len(args):
                    raise ValueError("arity conflict for %s in rule %s"
                                     % (name, r))
                if not neg:
                    pos_vars.update(args)
            for neg, name, args in r.body:
                if neg:
                    missing = [a for a in args if a not in pos_vars]
                    if missing:
                        raise ValueError("negated %s uses variables absent "
                                         "from positive literals in %s"
                                         % (name, r))
            missing = [a for a in r.head_args if a not in pos_vars]
            if missing:
                raise ValueError("head variables must appear in a positive "
                                 "literal in %s" % r)
        self.idb_arity = idb_arity
        self.all_arity = dict(self.base)
        self.all_arity.update(idb_arity)

    def _build_program(self):
        names = list(self.all_arity)
        pos_edges = {n: set() for n in names}
        neg_edges = {n: set() for n in names}
        self.rules_by_head = {}
        for r in self.rules:
            self.rules_by_head.setdefault(r.head, []).append(r)
            for neg, name, _ in r.body:
                (neg_edges if neg else pos_edges)[r.head].add(name)
        self.pos_edges = pos_edges
        self.neg_edges = neg_edges

        # Tarjan on positive edges; components are emitted sink-first,
        # i.e. the bottom-up evaluation order.
        idx = [0]
        stack, on_stack = [], set()
        indices, low = {}, {}
        comps = []

        def strong(v):
            indices[v] = low[v] = idx[0]
            idx[0] += 1
            stack.append(v)
            on_stack.add(v)
            for w in pos_edges[v]:
                if w not in indices:
                    strong(w)
                    low[v] = min(low[v], low[w])
                elif w in on_stack:
                    low[v] = min(low[v], indices[w])
            if low[v] == indices[v]:
                comp = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp.append(w)
                    if w == v:
                        break
                comps.append(comp)

        old_limit = sys.getrecursionlimit()
        sys.setrecursionlimit(max(old_limit, 10000))
        try:
            for n in names:
                if n not in indices:
                    strong(n)
        finally:
            sys.setrecursionlimit(old_limit)
        self.components = comps
        self.comp_of = {n: k for k, comp in enumerate(comps) for n in comp}
        for head, deps in neg_edges.items():
            for dep in deps:
                if self.comp_of[head] == self.comp_of[dep]:
                    raise ValueError(
                        "negative recursion through %s/%s is not allowed"
                        % (head, dep))
        self.rel_referrers = {n: set() for n in names}
        for r in self.rules:
            for _, name, _ in r.body:
                self.rel_referrers[name].add(r.head)

    # ------------------------------------------------------------- index/store
    def _store(self, name, tup, f):
        # Empty functions are retained during a batch (deletions still need
        # to be enumerable) and pruned by apply() once propagation ends.
        rel = self.store[name]
        rel[tup] = f
        if f:
            cols = self.indexes[name]
            for k, value in enumerate(tup):
                cols[k].setdefault(value, set()).add(tup)

    def _lookup(self, name, partial):
        """Present tuples matching a column->value partial binding."""
        rel = self.store[name]
        if not any(rel.values()):
            return ()
        if not partial:
            return [t for t, f in rel.items() if f]
        cols = self.indexes[name]
        candidates = None
        for k, value in sorted(partial.items(),
                               key=lambda kv: len(cols[kv[0]]
                                                  .get(kv[1], ()))):
            tuples = cols[k].get(value)
            if not tuples:
                return ()
            candidates = set(tuples) if candidates is None \
                else candidates & tuples
            if not candidates:
                return ()
        return [t for t in candidates if rel.get(t)]

    # -------------------------------------------------------------------- apply
    def apply(self, changes):
        self._validate_changes(changes)
        # Tentative superposition of the whole batch; a negative base count
        # anywhere rejects the batch before any state is touched.
        tentative = {}          # (relation, tuple) -> count function
        for name, tup, lo, hi, delta in changes:
            tup = tuple(tup)
            key = (name, tup)
            if key in tentative:
                base_f = tentative[key]          # earlier change in batch
            else:
                base_f = self.store[name].get(tup, [])  # pre-batch value
            f = seg.seg_add(base_f, [[lo, hi, delta]])
            if seg.has_negative(f):
                return {}
            tentative[key] = f
        if any(not seg.is_valid(f) for f in tentative.values()):
            return {}

        # Pre-batch count functions of every touched tuple.
        snapshots = {}
        for (name, tup) in tentative:
            pre = [list(s) for s in self.store[name].get(tup, [])]
            snapshots.setdefault(name, {})[tup] = pre
            cols = self.indexes[name]
            for k, value in enumerate(tup):
                cols[k].setdefault(value, set()).add(tup)

        # Build pre/post count-function views for every affected base
        # relation.  Untouched tuples are shared; touched tuples come from
        # the snapshot (pre) or the tentative superposition (post).
        views = {}
        touched_by_rel = {}
        for (name, tup) in tentative:
            touched_by_rel.setdefault(name, {})[tup] = snapshots[name][tup]
        for name, touched in touched_by_rel.items():
            pre_view = {}
            post_view = {}
            # Every tuple currently known before the commit.
            for tup, f in self.store[name].items():
                pre_view[tup] = touched.get(tup, f)
                post_view[tup] = tentative.get((name, tup), f)
            # Touched tuples that are new in this batch (absent pre-batch).
            for tup in touched:
                pre_view.setdefault(tup, touched[tup])
                post_view[tup] = tentative[(name, tup)]
            views[name] = (pre_view, post_view)

        # Commit tentative base values (empty entries are retained during
        # propagation so deletions remain enumerable; pruned at the end).
        for (name, tup), f in tentative.items():
            self.store[name][tup] = f
            if f:
                cols = self.indexes[name]
                for k, value in enumerate(tup):
                    cols[k].setdefault(value, set()).add(tup)

        changed_rels = sorted({name for name, _ in tentative},
                              key=lambda n: self.comp_of[n])
        settled_pre, _settled_post = self._propagate(
            changed_rels, tentative, views)

        # Prune emptied derived tuples now that no rule needs to enumerate
        # them.  Base relations are pruned only from their own tentative
        # entries, never as a side effect of derived recomputation.
        for (name, tup), f in tentative.items():
            if not f and tup in self.store[name]:
                del self.store[name][tup]
        for name in self.idb_arity:
            dead = [t for t, f in self.store[name].items() if not f]
            for t in dead:
                del self.store[name][t]

        result = {}
        for name in self.idb_arity:
            entries = []
            old_rel = settled_pre.get(name, {})
            for tup, f in self.store[name].items():
                diff = seg.indicator_diff(
                    seg.indicator(old_rel.get(tup, [])), f)
                for lo, hi, v in diff:
                    entries.append([tup, lo, hi, 1 if v > 0 else -1])
            for tup, old_f in old_rel.items():
                if tup not in self.store[name]:
                    for lo, hi, _v in seg.indicator(old_f):
                        entries.append([tup, lo, hi, -1])
            if entries:
                entries.sort(key=lambda e: (e[0], e[1]))
                result[name] = entries
        return result

    def _validate_changes(self, changes):
        if not isinstance(changes, list):
            raise ValueError("changes must be a list")
        seen = set()
        for ch in changes:
            if not isinstance(ch, (list, tuple)) or len(ch) != 5:
                raise ValueError("each change needs 5 fields: %r" % (ch,))
            name, tup, lo, hi, delta = ch
            if name not in self.base:
                raise ValueError("changes can only target base relations, "
                                 "got %r" % name)
            if not isinstance(tup, (list, tuple)) \
                    or len(tup) != self.base[name] \
                    or not all(isinstance(a, str) for a in tup):
                raise ValueError("invalid tuple for %s: %r" % (name, tup))
            if isinstance(lo, bool) or isinstance(hi, bool) \
                    or isinstance(delta, bool) \
                    or not all(isinstance(x, int)
                               for x in (lo, hi, delta)):
                raise ValueError("interval endpoints and delta must be ints")
            if lo >= hi or delta == 0:
                raise ValueError("need start < end and non-zero delta")
            key = (name, tuple(tup), lo, hi, delta)
            if key in seen:
                raise ValueError("duplicate change entry: %r" % (ch,))
            seen.add(key)

    # ------------------------------------------------------------- propagation
    def _propagate(self, changed_rels, tentative, views):
        """Stratified, incremental fixpoint.

        Non-recursive components are recomputed once as a pre/post whole
        product difference restricted to rules whose body references a
        changed relation (self-joins are then exact).  Recursive components
        run a count-based semi-naive delta closure.  Rules with negation
        fire after the positive fixpoint of their stratum.
        """
        # Which relations actually changed per component.
        changed_by_comp = {}
        for name in changed_rels:
            changed_by_comp.setdefault(self.comp_of[name], set()).add(name)
        # Track derived relations once their component settles.  Every
        # relation starts with its pre-batch value so net-change diffing
        # works even when a component is untouched by the batch.
        settled_pre = {n: {t: [list(s) for s in f]
                           for t, f in self.store[n].items()}
                       for n in self.idb_arity}
        settled_post = {n: {t: [list(s) for s in f]
                            for t, f in self.store[n].items()}
                        for n in self.idb_arity}

        for k, comp in enumerate(self.components):
            # Base-only components have no rules: their values were
            # committed directly and must never be recomputed.
            heads = [n for n in comp if n in self.idb_arity]
            if not heads:
                continue
            if not self._component_touches(comp, changed_by_comp, k,
                                          settled_pre, settled_post):
                continue
            recursive = self._is_recursive(comp)
            if recursive:
                self._fixpoint_component(k, comp, changed_by_comp,
                                         settled_pre, settled_post, views)
            else:
                self._recompute_component(k, comp[0], changed_by_comp,
                                          settled_pre, settled_post, views)
        return settled_pre, settled_post

    def _is_recursive(self, comp):
        for head in comp:
            for rule in self.rules_by_head.get(head, []):
                for _, dep, _ in rule.body:
                    if dep in comp:
                        return True
        return False

    def _component_touches(self, comp, changed_by_comp, k,
                           settled_pre, settled_post):
        if k in changed_by_comp:
            return True
        for head in comp:
            for rule in self.rules_by_head.get(head, []):
                deps = {name for _, name, _ in rule.body}
                if self._deps_changed(deps, changed_by_comp, k,
                                      settled_pre, settled_post):
                    return True
        return False

    def _recompute_component(self, k, head, changed_by_comp,
                             settled_pre, settled_post, views):
        # Pre-batch value of this head, before any rule is re-evaluated.
        pre_snapshot = {t: [list(s) for s in f]
                        for t, f in self.store[head].items()}
        # Re-evaluate every rule defining this head.  Rules whose
        # dependencies did not change produce identical pre and post
        # products and therefore contribute a zero delta, so including
        # them is safe and keeps alternative proofs intact.
        relevant_rules = self.rules_by_head.get(head, [])
        pre_acc, post_acc = {}, {}
        for rule in relevant_rules:
            rule_has_neg = any(n for n, _, _ in rule.body)
            pre_p = self._rule_product(rule, post=False, views=views,
                                       settled_pre=settled_pre,
                                       settled_post=settled_post,
                                       use_post_for_neg=rule_has_neg)
            post_p = self._rule_product(rule, post=True, views=views,
                                        settled_pre=settled_pre,
                                        settled_post=settled_post,
                                        use_post_for_neg=rule_has_neg)
            for t, f in pre_p.items():
                pre_acc[t] = seg.seg_add(pre_acc.get(t, []), f)
            for t, f in post_p.items():
                post_acc[t] = seg.seg_add(post_acc.get(t, []), f)
        # Derived relation value = sum of rule proof counts.
        new_rel = {t: f for t, f in post_acc.items() if f}
        for t, f in new_rel.items():
            self.store[head][t] = f
        for t in list(self.store[head]):
            if t not in new_rel:
                self.store[head][t] = []
        settled_pre[head] = pre_snapshot
        settled_post[head] = new_rel
        if pre_snapshot != new_rel:
            changed_by_comp.setdefault(k, set()).add(head)

    def _deps_changed(self, deps, changed_by_comp, k,
                      settled_pre, settled_post):
        for dep in deps:
            if dep in self.base:
                cid = self.comp_of[dep]
                if dep in changed_by_comp.get(cid, set()):
                    return True
            elif dep in self.idb_arity:
                pre = settled_pre.get(dep)
                post = settled_post.get(dep)
                if post is not None and pre is not None and pre != post:
                    return True
        return False

    def _fixpoint_component(self, k, comp, changed_by_comp,
                            settled_pre, settled_post, views):
        # Pre-batch values of every relation in the recursive component.
        pre_values = {name: {t: [list(s) for s in f]
                             for t, f in self.store[name].items()}
                      for name in comp}

        # 1) Affected cone: the finite set of component tuples whose
        #    derivations can touch a tuple that changed in this batch.
        cone = self._build_cone(comp, views, settled_pre, settled_post)

        # 2) Existence (indicator) least fixpoint of the post world inside
        #    the cone.  Indicators over a finite tuple domain form a
        #    monotone operator that converges in finitely many rounds even
        #    with cycles; a cyclic tuple with no external support never
        #    becomes true.  Starting empty yields the least fixpoint.
        positive_rules = [(head, rule) for head in comp
                          for rule in self.rules_by_head.get(head, [])
                          if not any(n for n, _, _ in rule.body)]
        exist_state = {name: {} for name in comp}  # tuple -> indicator seg
        rounds = 0
        while True:
            rounds += 1
            if rounds > 10000:
                raise AssertionError(
                    "recursive fixpoint did not converge: %s" % comp)
            nxt = {name: {} for name in comp}
            for head, rule in positive_rules:
                product = self._rule_product(
                    rule, post=True, views=views,
                    settled_pre=settled_pre, settled_post=settled_post,
                    use_post_for_neg=False, override=exist_state)
                for t, f in product.items():
                    ind = seg.indicator(f)
                    nxt[head][t] = seg.seg_add(
                        nxt[head].get(t, []), ind)
                    cone.add((head, t))
            if nxt == exist_state:
                break
            exist_state = nxt
        exist_sets = {name: set(exist_state[name]) for name in comp}

        # 3) The settled indicator tables are already the final interval
        #    values: recursive relations have existence semantics, so a
        #    tuple's value is exactly the indicator of its union of proofs.
        #    Base and lower-stratum relations keep their real counts and
        #    enter the products unchanged.
        cone_state = {name: {t: [list(s) for s in f]
                             for t, f in exist_state[name].items()}
                      for name in comp}

        # 4) Commit post values for cone tuples; tuples outside the cone
        #    are provably unaffected and keep their pre-batch values.
        post_values = {name: dict(pre_values[name]) for name in comp}
        for name in comp:
            for t, f in cone_state[name].items():
                post_values[name][t] = f
            stale = [t for t in list(post_values[name])
                     if (name, t) in cone and t not in cone_state[name]]
            for t in stale:
                post_values[name].pop(t, None)
        for name in comp:
            for t, f in post_values[name].items():
                self.store[name][t] = f
            for t in list(self.store[name]):
                if (name, t) in cone and t not in post_values[name]:
                    self.store[name][t] = []

        # 4) Stratified negation rules fire after the positive fixpoint.
        for head in comp:
            for rule in self.rules_by_head.get(head, []):
                if not any(n for n, _, _ in rule.body):
                    continue
                if any(neg and self.comp_of[name] == k
                       for neg, name, _ in rule.body):
                    raise ValueError("negative recursion rejected")
                pre_p = self._rule_product(
                    rule, post=False, views=views,
                    settled_pre=settled_pre, settled_post=settled_post,
                    use_post_for_neg=True, override=pre_values)
                post_p = self._rule_product(
                    rule, post=True, views=views,
                    settled_pre=settled_pre, settled_post=settled_post,
                    use_post_for_neg=True, override=post_values)
                for t, f in pre_p.items():
                    self.store[head][t] = seg.seg_add(
                        self.store[head].get(t, []),
                        seg.seg_negate(f))
                for t, f in post_p.items():
                    self.store[head][t] = seg.seg_add(
                        self.store[head].get(t, []), f)
            settled_pre[head] = pre_values[head]
            settled_post[head] = {t: f for t, f in
                                  self.store[head].items() if f}
            changed_by_comp.setdefault(k, set()).add(head)

    def _build_cone(self, comp, views, settled_pre, settled_post):
        """Enumerate every component tuple reachable from a changed fact.

        A changed external tuple is pinned in each rule that references
        its relation; index-driven binding enumeration yields the head
        tuples, which become new frontier facts until the cone closes.
        """
        seeds = set()
        for seed_rel in self._external_seeds(comp):
            pre_v, post_v = self._relation_views(
                seed_rel, views, settled_pre, settled_post)
            for t in set(pre_v) | set(post_v):
                if pre_v.get(t) != post_v.get(t):
                    seeds.add((seed_rel, t))
        cone = set()
        frontier = list(seeds)
        while frontier:
            rel, tup = frontier.pop(0)
            for head in comp:
                for rule in self.rules_by_head.get(head, []):
                    if not any(name == rel for _, name, _ in rule.body):
                        continue
                    for ht in self._head_tuples(rule, rel, tup, comp,
                                                cone_state=None,
                                                views=views):
                        fact = (head, ht)
                        if fact not in cone:
                            cone.add(fact)
                            frontier.append(fact)
        # External seeds themselves are not component facts.
        return cone

    def _head_tuples(self, rule, pinned_rel, pinned_tup, comp,
                     cone_state, views):
        found = set()
        seed_positions = [i for i, (_, name, args) in enumerate(rule.body)
                          if name == pinned_rel
                          and len(args) == len(pinned_tup)]
        for seed_pos in seed_positions:
            order = self._order_from_seed(rule, seed_pos)
            binding0 = dict(zip(rule.body[seed_pos][2], pinned_tup))

            def recurse(idx, binding):
                if idx == len(order):
                    found.add(tuple(binding[a] for a in rule.head_args))
                    return
                lit_pos = order[idx]
                neg, name, args = rule.body[lit_pos]
                if lit_pos == seed_pos:
                    recurse(idx + 1, binding)
                    return
                if neg:
                    recurse(idx + 1, binding)
                    return
                partial = {k: binding[a] for k, a in enumerate(args)
                           if a in binding}
                if name in comp:
                    rel = self.store[name]
                elif name in views:
                    rel = views[name][1]
                elif name in self.base:
                    rel = self.store[name]
                else:
                    rel = {}
                for t in rel:
                    if not rel[t] or not self._matches(t, partial):
                        continue
                    local = dict(zip(args, t))
                    if any(binding.get(var) is not None
                           and binding[var] != val
                           for var, val in local.items()):
                        continue
                    nb = dict(binding)
                    nb.update(local)
                    recurse(idx + 1, nb)

            recurse(0, binding0)
        return found

    def _external_seeds(self, comp):
        seeds = set()
        for head in comp:
            for rule in self.rules_by_head.get(head, []):
                for _, name, _ in rule.body:
                    if name not in comp or self.comp_of[name] != \
                            self.comp_of[head]:
                        seeds.add(name)
        return seeds

    def _relation_views(self, name, views, settled_pre, settled_post):
        if name in views:
            return views[name]
        return settled_pre.get(name, {}), settled_post.get(name, {})

    # ------------------------------------------------------------- rule engine
    def _rule_product(self, rule, post, views, settled_pre,
                      settled_post, use_post_for_neg, override=None):
        """Full proof-count product of a rule under one world view.

        Returns head tuple -> count segment function.  Positive literals are
        read from the pre or post world; negated literals remove the time
        points where their tuple exists.  Enumeration is index driven.
        """
        out = {}
        world_post = post

        def literal_value(name, tup):
            if override is not None and name in override:
                return override[name].get(tup, [])
            if name in views:
                v = views[name][1 if world_post else 0]
                return v.get(tup, [])
            if name in self.base:
                # Untouched base relation: identical in both worlds.
                return self.store[name].get(tup, [])
            rel = settled_post if world_post else settled_pre
            return rel.get(name, {}).get(tup, [])

        def literal_rows(name, partial):
            if override is not None and name in override:
                rel = override[name]
                return [t for t in rel if self._matches(t, partial)]
            if name in views:
                rel = views[name][1 if world_post else 0]
                return [t for t in rel if rel[t] and
                        self._matches(t, partial)]
            if name in self.base:
                rel = self.store[name]
                return [t for t, f in rel.items()
                        if f and self._matches(t, partial)]
            rel = (settled_post if world_post else settled_pre).get(
                name, {})
            return [t for t in rel if rel[t] and self._matches(t, partial)]

        order = self._order_literals(rule)

        def recurse(idx, binding, factor):
            if not factor:
                return
            if idx == len(order):
                head_tup = tuple(binding[a] for a in rule.head_args)
                out[head_tup] = seg.seg_add(out.get(head_tup, []), factor)
                return
            neg, name, args = order[idx]
            if neg:
                tup = tuple(binding[a] for a in args)
                presence = seg.indicator(self._neg_value(
                    name, tup, world_post, views,
                    settled_pre, settled_post, override))
                recurse(idx + 1, binding, seg.cut(factor, presence))
                return
            partial = {k: binding[a] for k, a in enumerate(args)
                       if a in binding}
            for tup in literal_rows(name, partial):
                local = dict(zip(args, tup))
                if any(binding.get(var) is not None
                       and binding[var] != val
                       for var, val in local.items()):
                    continue
                f = literal_value(name, tup)
                nb = dict(binding)
                nb.update(local)
                recurse(idx + 1, nb, seg.seg_mul(factor, f))

        bounds = self._world_bounds(rule, views, settled_pre,
                                    settled_post, world_post)
        recurse(0, {}, [[bounds[0], bounds[1], 1]] if bounds else [])
        return out

    def _neg_value(self, name, tup, world_post, views,
                   settled_pre, settled_post, override=None):
        # A negated literal observes the same world (pre or post) as the
        # positive literals; stratification guarantees its relation belongs
        # to a strictly lower, already settled component.
        if override is not None and name in override:
            return override[name].get(tup, [])
        if name in views:
            return views[name][1 if world_post else 0].get(tup, [])
        if name in self.base:
            return self.store[name].get(tup, [])
        rel = settled_post if world_post else settled_pre
        return rel.get(name, {}).get(tup, [])

    def _world_bounds(self, rule, views, settled_pre, settled_post, post):
        bounds = []
        for _, name, _ in rule.body:
            if name in views:
                rel = views[name][1 if post else 0]
            elif name in self.base:
                rel = self.store[name]
            else:
                rel = (settled_post if post else settled_pre).get(
                    name, {})
            for f in rel.values():
                bounds.extend(s[0] for s in f)
                bounds.extend(s[1] for s in f)
        if not bounds:
            return None
        return min(bounds), max(bounds)

    @staticmethod
    def _matches(tup, partial):
        return all(tup[k] == v for k, v in partial.items())

    def _order_literals(self, rule):
        rest = list(range(len(rule.body)))
        bound = set()
        order = []
        while rest:
            def score(i):
                neg, _, args = rule.body[i]
                have = sum(1 for a in args if a in bound)
                return (0 if have == len(args) else 1,
                        1 if neg else 0, -have)
            pick = min(rest, key=score)
            rest.remove(pick)
            order.append(rule.body[pick])
            bound.update(rule.body[pick][2])
        return order

    def _order_from_seed(self, rule, seed_pos):
        rest = [i for i in range(len(rule.body)) if i != seed_pos]
        bound = set(rule.body[seed_pos][2])
        order = [seed_pos]
        while rest:
            def score(i):
                neg, _, args = rule.body[i]
                have = sum(1 for a in args if a in bound)
                return (0 if have == len(args) else 1,
                        1 if neg else 0, -have)
            pick = min(rest, key=score)
            rest.remove(pick)
            order.append(pick)
            bound.update(rule.body[pick][2])
        return order

    # -------------------------------------------------------------------- read
    def read(self, name):
        if name not in self.all_arity:
            raise ValueError("unknown relation: %r" % name)
        out = []
        for tup, f in self.store[name].items():
            for lo, hi, _v in seg.indicator(f):
                out.append([tup, lo, hi])
        out.sort(key=lambda e: (e[0], e[1]))
        return out
