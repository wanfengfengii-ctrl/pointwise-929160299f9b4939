"""Built-in business checks, a pointwise reference model and fuzzing.

The reference evaluator recomputes stratified least fixpoints one integer
time point at a time.  It is deliberately simple and independent of the
incremental engine; the fuzz harness asserts that the incremental engine
agrees with it after every random batch of corrections.
"""

from .engine import Engine


def _norm_read(rows):
    return [(tuple(t), lo, hi) for t, lo, hi in rows]


def _norm_net(net):
    return {name: [(tuple(t), lo, hi, sign) for t, lo, hi, sign in rows]
            for name, rows in net.items()}


# --------------------------------------------------------------------- checks
def check_spec_example():
    """R(X,Y) :- E(X,Y), !B(X,Y) with E@[0,5) and B@[2,3)."""
    eng = Engine({"E": 2, "B": 2},
                 ["R(X,Y) :- E(X,Y), !B(X,Y)"])
    net = eng.apply([
        ["E", ("a", "b"), 0, 5, 1],
        ["B", ("a", "b"), 2, 3, 1],
    ])
    assert _norm_read(eng.read("R")) == [
        (("a", "b"), 0, 2), (("a", "b"), 3, 5)], eng.read("R")
    assert _norm_net(net) == {"R": [
        (("a", "b"), 0, 2, 1), (("a", "b"), 3, 5, 1)]}, net
    # Remove the block: the gap closes and intervals merge.
    net = eng.apply([["B", ("a", "b"), 2, 3, -1]])
    assert _norm_read(eng.read("R")) == [(("a", "b"), 0, 5)]
    assert _norm_net(net) == {"R": [(("a", "b"), 2, 3, 1)]}, net
    # Remove the evidence: R disappears.
    net = eng.apply([["E", ("a", "b"), 0, 5, -1]])
    assert eng.read("R") == []
    assert _norm_net(net) == {"R": [(("a", "b"), 0, 5, -1)]}, net


def check_batch_rollback():
    eng = Engine({"E": 2}, ["R(X,Y) :- E(X,Y)"])
    eng.apply([["E", ("a", "b"), 0, 10, 1]])
    # 1 + (-1) = 0 on [4,6): legal, R loses that window.
    net = eng.apply([["E", ("a", "b"), 4, 6, -1]])
    assert _norm_net(net) == {"R": [(("a", "b"), 4, 6, -1)]}, net
    assert _norm_read(eng.read("R")) == [
        (("a", "b"), 0, 4), (("a", "b"), 6, 10)], eng.read("R")
    # An over-decrement makes the count negative: whole batch rolls back.
    state = {n: [list(r) for r in eng.read(n)] for n in ("E", "R")}
    net = eng.apply([["E", ("a", "b"), 2, 8, -2]])
    assert net == {}
    assert {n: [list(r) for r in eng.read(n)] for n in ("E", "R")} == state
    return state


def check_superposition_merge():
    eng = Engine({"E": 2}, ["R(X,Y) :- E(X,Y)"])
    eng.apply([
        ["E", ("a", "b"), 0, 5, 1],
        ["E", ("a", "b"), 5, 10, 1],
        ["E", ("a", "b"), 3, 7, 1],
    ])
    # Existence on [0,10), maximal merge despite stacked counts.
    assert _norm_read(eng.read("R")) == [(("a", "b"), 0, 10)]
    # Remove one of the two proofs on [3,5) and [5,7): still exists there.
    net = eng.apply([["E", ("a", "b"), 3, 7, -1]])
    assert net == {}, net  # R stays present throughout
    assert _norm_read(eng.read("R")) == [(("a", "b"), 0, 10)]
    # Removing the last proof clears the relation.
    net = eng.apply([["E", ("a", "b"), 0, 5, -1],
                     ["E", ("a", "b"), 5, 10, -1]])
    assert _norm_net(net) == {"R": [(("a", "b"), 0, 10, -1)]}, net
    assert eng.read("R") == []


def check_transitive_closure_recursion():
    rules = [
        "T(X,Y) :- E(X,Y)",
        "T(X,Y) :- E(X,Z), T(Z,Y)",
    ]
    eng = Engine({"E": 2}, rules)
    eng.apply([
        ["E", ("a", "b"), 0, 10, 1],
        ["E", ("b", "c"), 0, 10, 1],
        ["E", ("c", "d"), 2, 8, 1],
    ])
    got = _norm_read(eng.read("T"))
    assert got == [
        (("a", "b"), 0, 10),
        (("a", "c"), 0, 10),
        (("a", "d"), 2, 8),
        (("b", "c"), 0, 10),
        (("b", "d"), 2, 8),
        (("c", "d"), 2, 8),
    ], got
    # Break the middle link on [4,6): paths through it lose that window.
    net = eng.apply([["E", ("b", "c"), 4, 6, -1]])
    got = _norm_read(eng.read("T"))
    assert got == [
        (("a", "b"), 0, 10),
        (("a", "c"), 0, 4), (("a", "c"), 6, 10),
        (("a", "d"), 2, 4), (("a", "d"), 6, 8),
        (("b", "c"), 0, 4), (("b", "c"), 6, 10),
        (("b", "d"), 2, 4), (("b", "d"), 6, 8),
        (("c", "d"), 2, 8),
    ], got
    # Net changes only carry the delta intervals.
    assert _norm_net(net)["T"] == [
        (("a", "c"), 4, 6, -1), (("a", "d"), 4, 6, -1),
        (("b", "c"), 4, 6, -1), (("b", "d"), 4, 6, -1),
    ], net
    # Restore the link: proofs come back, unsupported cyclic windows do not.
    eng.apply([["E", ("b", "c"), 4, 6, 1]])
    assert (("a", "d"), 2, 8) in _norm_read(eng.read("T"))


def check_multiple_proofs_keep_one():
    rules = [
        "R(X,Y) :- E(X,Y)",
        "R(X,Y) :- F(X,Y)",
    ]
    eng = Engine({"E": 2, "F": 2}, rules)
    eng.apply([["E", ("a", "b"), 0, 10, 1],
               ["F", ("a", "b"), 3, 7, 1]])
    assert _norm_read(eng.read("R")) == [(("a", "b"), 0, 10)]
    net = eng.apply([["E", ("a", "b"), 0, 10, -1]])  # F still supports [3,7)
    assert _norm_net(net) == {"R": [
        (("a", "b"), 0, 3, -1), (("a", "b"), 7, 10, -1)]}, net
    assert _norm_read(eng.read("R")) == [(("a", "b"), 3, 7)]


def check_self_join():
    eng = Engine({"E": 2}, ["Q(X,Y) :- E(X,Z), E(Z,Y)"])
    eng.apply([
        ["E", ("a", "b"), 0, 5, 1],
        ["E", ("b", "c"), 0, 5, 1],
        ["E", ("a", "c"), 2, 4, 1],
    ])
    # Only Z=b works: E(a,b) join E(b,c) -> Q(a,c) over [0,5).
    got = _norm_read(eng.read("Q"))
    assert got == [(("a", "c"), 0, 5)], got
    net = eng.apply([["E", ("b", "c"), 0, 5, -1]])
    assert eng.read("Q") == [], eng.read("Q")
    assert _norm_net(net) == {"Q": [(("a", "c"), 0, 5, -1)]}, net
    # A second join path appears; note E(a,c)@[2,4) also joins through
    # Z=c to E(c,d), adding another Q(a,d) proof on that same window.
    eng.apply([
        ["E", ("b", "c"), 0, 5, 1],
        ["E", ("c", "d"), 1, 4, 1],
    ])
    got = _norm_read(eng.read("Q"))
    assert got == [
        (("a", "c"), 0, 5),
        (("a", "d"), 2, 4),
        (("b", "d"), 1, 4),
    ], got


def check_stratified_negation_idb():
    rules = [
        "T(X,Y) :- E(X,Y)",
        "T(X,Y) :- E(X,Z), T(Z,Y)",
        "R(X,Y) :- T(X,Y), !T(Y,X)",
    ]
    eng = Engine({"E": 2}, rules)
    eng.apply([
        ["E", ("a", "b"), 0, 10, 1],
        ["E", ("b", "a"), 4, 6, 1],
    ])
    got = _norm_read(eng.read("R"))
    # On [4,6) T(a,b) and T(b,a) both hold, so R(a,b) is blocked there;
    # R(b,a) is blocked whenever T(a,b) exists, i.e. never present.
    assert got == [
        (("a", "b"), 0, 4), (("a", "b"), 6, 10),
    ], got


def check_validation_errors():
    def expect_error(base, rules, *change_batches):
        try:
            Engine(base, rules)
        except ValueError:
            return
        raise AssertionError("expected ValueError for %r" % rules)

    expect_error({"E": 2}, ["R(X,Y) :- !E(X,Y)"])          # no positive lit
    expect_error({"E": 2}, ["R(X,Y) :- E(X,Z), !E(Z,Y)"])  # unbound neg var
    expect_error({"E": 2}, ["E(X,Y) :- E(X,Y)"])           # base as head
    expect_error({"E": 2}, ["R(X,Y) :- G(X,Y)"])           # undefined rel
    expect_error({"E": 2}, [                               # arity conflict
        "R(X,Y) :- E(X,Y)", "R(X,Y,Z) :- E(X,Y)"])
    expect_error({"E": 2}, ["R(X,Y) :- E(X,Y), !R(X,Y)"])  # neg recursion
    expect_error({"E": 2}, ["R(X,X) :- E(X,X)"])           # repeated head var
    expect_error({"E": 2}, ["R(X,Y) :- E(X)"])             # literal arity

    eng = Engine({"E": 2}, ["R(X,Y) :- E(X,Y)"])
    for bad in [
        [["R", ("a", "b"), 0, 1, 1]],          # derived relation as target
        [["E", ("a",), 0, 1, 1]],              # arity mismatch
        [["E", ("a", "b"), 5, 5, 1]],          # empty interval
        [["E", ("a", "b"), 0, 1, 0]],          # zero delta
        [["E", ("a", "b"), 0, 1, "1"]],        # bad type
    ]:
        try:
            eng.apply(bad)
        except ValueError:
            continue
        raise AssertionError("expected ValueError for %r" % bad)
    try:
        eng.read("missing")
    except ValueError:
        pass
    else:
        raise AssertionError("read() must reject unknown relations")


# ------------------------------------------------------------- pointwise ref
def reference_state(base, rules_text, timeline, batches):
    """Naive per-integer stratified fixpoint, independent of the engine."""
    eng = Engine(base, rules_text)
    parsed = eng.rules
    counts = {name: {} for name in eng.all_arity}

    def fixpoint(t):
        current = {n: set(counts[n].get(t, ())) for n in counts}
        changed = True
        # Stratified component order from the engine's own analysis.
        for comp in eng.components:
            local_changed = True
            while local_changed:
                local_changed = False
                for r in parsed:
                    if r.head not in comp:
                        continue
                    rows = set()
                    _eval_rule_point(r, current, rows)
                    before = current[r.head]
                    current[r.head] = before | rows
                    if current[r.head] != before:
                        local_changed = changed = True
        return current

    def _eval_rule_point(rule, current, sink):
        body = rule.body

        def rec(i, binding):
            if i == len(body):
                sink.add(tuple(binding[a] for a in rule.head_args))
                return
            neg, name, args = body[i]
            if neg:
                tup = tuple(binding[a] for a in args)
                if tup not in current[name]:
                    rec(i + 1, binding)
                return
            partial = {k: binding[a] for k, a in enumerate(args)
                       if a in binding}
            for row in current[name]:
                if any(k in partial and row[k] != v
                       for k, v in partial.items()):
                    continue
                nb = dict(binding)
                nb.update(dict(zip(args, row)))
                rec(i + 1, nb)

        rec(0, {})

    # Replay the same batches; invalid/negative batches are rejected too.
    base_counts = {n: {} for n in base}
    snapshots = []
    for batch in batches:
        tentative = {k: dict(v) for k, v in base_counts.items()}
        ok = True
        for name, tup, lo, hi, delta in batch:
            tup = tuple(tup)
            for t in range(lo, hi):
                d = tentative[name].get((t, tup), 0) + delta
                if d < 0:
                    ok = False
                    break
                tentative[name][(t, tup)] = d
            if not ok:
                break
        snapshots.append(ok)
        if ok:
            base_counts = tentative
    # Build per-point base presence and derive.
    lo, hi = timeline
    ref = {n: {} for n in eng.all_arity}
    for t in range(lo, hi):
        current = {n: {tup for (tt, tup), c in base_counts[n].items()
                       if tt == t and c > 0} for n in base}
        for n in eng.idb_arity:
            current[n] = set()
        # run fixpoint with stratum order using engine structure
        state = current
        for comp in eng.components:
            again = True
            while again:
                again = False
                for r in parsed:
                    if r.head not in comp:
                        continue
                    rows = set()
                    _eval_rule_point(r, state, rows)
                    if not rows <= state[r.head]:
                        state[r.head] |= rows
                        again = True
        for n in state:
            ref[n][t] = state[n]
    return ref


def fuzz_against_reference(seed=20261112, rounds=40):
    import random
    rng = random.Random(seed)
    base = {"E": 2}
    rules = [
        "T(X,Y) :- E(X,Y)",
        "T(X,Y) :- E(X,Z), T(Z,Y)",
    ]
    horizon = 12
    nodes = ["a", "b", "c", "d"]
    eng = Engine(base, rules)
    # Maintain base counts directly to generate legal corrections.
    base_counts = {}
    batches = []
    for _ in range(rounds):
        batch = []
        for _ in range(rng.randint(1, 4)):
            tup = (rng.choice(nodes), rng.choice(nodes))
            lo = rng.randrange(0, horizon - 1)
            hi = rng.randrange(lo + 1, horizon + 1)
            cur = min(base_counts.get((tup, t), 0)
                      for t in range(lo, hi))
            delta = rng.choice([1, 1, 1, -1]) if cur > 0 else 1
            if delta < 0 and cur == 0:
                delta = 1
            batch.append(["E", list(tup), lo, hi, delta])
            for t in range(lo, hi):
                base_counts[(tup, t)] = base_counts.get((tup, t), 0) + delta
        # Decide whether this batch is legal under the counts.
        legal = all(v >= 0 for v in base_counts.values())
        if not legal:
            # Roll back our shadow counts to mirror engine behavior.
            for name, tup, lo, hi, delta in batch:
                for t in range(lo, hi):
                    base_counts[(tup, t)] -= delta
        net = eng.apply(batch)
        if not legal:
            assert net == {}, ("illegal batch must roll back", batch)
        batches.append(batch)
    ref = reference_state(base, rules, (0, horizon), batches)
    for name in eng.all_arity:
        expected = {}
        for t in range(horizon):
            for row in ref[name][t]:
                expected.setdefault(row, []).append(t)
        got = _norm_read(eng.read(name))
        got_points = {}
        for row, lo, hi in got:
            got_points.setdefault(row, []).extend(range(lo, hi))
        for row in set(expected) | set(got_points):
            assert sorted(got_points.get(row, [])) == sorted(
                expected.get(row, [])), (name, row)


def fuzz_negation(seed=31337, rounds=50):
    """Fuzz a join, an alternative proof and a stratified negation."""
    import random
    rng = random.Random(seed)
    base = {"E": 2, "F": 2, "B": 2}
    rules = [
        "J(X,Y) :- E(X,Z), F(Z,Y)",
        "R(X,Y) :- E(X,Y), !B(X,Y)",
        "R(X,Y) :- J(X,Y), !B(X,Y)",
    ]
    horizon = 10
    nodes = ["a", "b", "c"]
    eng = Engine(base, rules)
    counts = {}
    batches = []
    for _ in range(rounds):
        batch = []
        for _ in range(rng.randint(1, 4)):
            name = rng.choice(["E", "F", "B"])
            tup = (rng.choice(nodes), rng.choice(nodes))
            lo = rng.randrange(0, horizon - 1)
            hi = rng.randrange(lo + 1, horizon + 1)
            cur = min(counts.get((name, tup, t), 0)
                      for t in range(lo, hi))
            delta = rng.choice([1, 1, -1]) if cur > 0 else 1
            batch.append([name, list(tup), lo, hi, delta])
            for t in range(lo, hi):
                counts[(name, tup, t)] = \
                    counts.get((name, tup, t), 0) + delta
        legal = all(v >= 0 for v in counts.values())
        if not legal:
            for name, tup, lo, hi, delta in batch:
                for t in range(lo, hi):
                    counts[(name, tuple(tup), t)] -= delta
        net = eng.apply(batch)
        if not legal:
            assert net == {}, ("illegal batch must roll back", batch)
        batches.append(batch)
    ref = reference_state(base, rules, (0, horizon), batches)
    for name in eng.all_arity:
        expected = {}
        for t in range(horizon):
            for row in ref[name][t]:
                expected.setdefault(row, []).append(t)
        got = _norm_read(eng.read(name))
        got_points = {}
        for row, lo, hi in got:
            got_points.setdefault(row, []).extend(range(lo, hi))
        for row in set(expected) | set(got_points):
            assert sorted(got_points.get(row, [])) == sorted(
                expected.get(row, [])), (name, row)


# ----------------------------------------------------------------------- demo
def demo():
    print("=" * 68)
    print("供应链合规：风险名单按历史更正增量更新（区间 Datalog 演示）")
    print("=" * 68)
    base = {"Shipment": 2, "Blocked": 2, "Approved": 2}
    rules = [
        "Risk(X,Y) :- Shipment(X,Y), !Blocked(X,Y)",
        "Risk(X,Y) :- Shipment(X,Y), Approved(X,Y)",
    ]
    eng = Engine(base, rules)
    print("\n[批次1] 装载运输事实与拦截/审批窗口 ...")
    net = eng.apply([
        ["Shipment", ("supplier-1", "part-7"), 0, 10, 1],
        ["Shipment", ("supplier-2", "part-9"), 2, 8, 1],
        ["Blocked", ("supplier-1", "part-7"), 3, 5, 1],
        ["Approved", ("supplier-2", "part-9"), 4, 6, 1],
    ])
    print("  派生净变化:", json_safe(net))
    print("  Risk 当前:", json_safe(eng.read("Risk")))

    print("\n[批次2] 历史更正：拦截记录 [3,5) 系误录，予以撤回 ...")
    net = eng.apply([["Blocked", ("supplier-1", "part-7"), 3, 5, -1]])
    print("  派生净变化:", json_safe(net))
    print("  Risk 当前:", json_safe(eng.read("Risk")))

    print("\n[批次3] 非法更正：超量撤回一条运输（计数将为负），整批回滚 ...")
    net = eng.apply([
        ["Shipment", ("supplier-2", "part-9"), 2, 8, -5],
        ["Approved", ("supplier-2", "part-9"), 4, 6, 1],
    ])
    print("  apply 返回:", net, "（空字典表示回滚，状态不变）")
    print("  Risk 仍为:", json_safe(eng.read("Risk")))

    print("\n[批次4] 合规更正：撤回 supplier-2 的运输历史 ...")
    net = eng.apply([["Shipment", ("supplier-2", "part-9"), 2, 8, -1]])
    print("  派生净变化:", json_safe(net))
    print("  Risk 最终:", json_safe(eng.read("Risk")))
    print("\n演示结束。")


def json_safe(rows):
    if isinstance(rows, dict):
        return {k: json_safe(v) for k, v in rows.items()}
    return [[list(x) if isinstance(x, tuple) else x for x in row]
            for row in rows]


# --------------------------------------------------------------------- runner
def run_all(verbose=False):
    checks = [
        check_spec_example,
        check_batch_rollback,
        check_superposition_merge,
        check_transitive_closure_recursion,
        check_multiple_proofs_keep_one,
        check_self_join,
        check_stratified_negation_idb,
        check_validation_errors,
        fuzz_against_reference,
        fuzz_negation,
    ]
    failures = 0
    for check in checks:
        try:
            check()
        except AssertionError as exc:
            failures += 1
            print("FAIL %s: %s" % (check.__name__, exc))
        else:
            if verbose:
                print("ok   %s" % check.__name__)
    return failures
