"""Sparse piecewise-constant "count functions" over half-open integer intervals.

A segment function is a sorted list of disjoint segments ``[lo, hi, value]``
where every segment carries a non-zero integer value.  All arithmetic is
driven by segment endpoints: intervals are split at boundaries only, so the
cost is proportional to the number of segments rather than the width of the
integer range (no per-integer expansion).
"""


def seg_add(f, g):
    """Pointwise addition of two segment functions.

    Adjacent segments carrying the same resulting value are merged, and
    segments whose value becomes zero are dropped.  The sweep visits every
    segment endpoint, so values that drop to zero and recover later are
    handled without losing the trailing segments.
    """
    if not f:
        return [list(s) for s in g]
    if not g:
        return [list(s) for s in f]
    points = sorted({p for s in f for p in s[:2]}
                    | {p for s in g for p in s[:2]})
    i = j = 0
    out = []
    for p, x in enumerate(points[:-1]):
        while i < len(f) and f[i][1] <= x:
            i += 1
        while j < len(g) and g[j][1] <= x:
            j += 1
        vf = f[i][2] if i < len(f) and f[i][0] <= x < f[i][1] else 0
        vg = g[j][2] if j < len(g) and g[j][0] <= x < g[j][1] else 0
        val = vf + vg
        if val == 0:
            continue
        end = points[p + 1]
        if out and out[-1][1] == x and out[-1][2] == val:
            out[-1][1] = end
        else:
            out.append([x, end, val])
    return out


def seg_negate(f):
    """Return the pointwise negation of a segment function."""
    return [[lo, hi, -v] for lo, hi, v in f]


def seg_mul(f, g, merge=True):
    """Pointwise product over the intersection of supports.

    Used for conjunction: a proof exists only where every literal is
    present.  When ``merge`` is true adjacent result segments with equal
    value are joined.
    """
    out = []
    if not f or not g:
        return out
    i = j = 0
    while i < len(f) and j < len(g):
        lo = max(f[i][0], g[j][0])
        hi = min(f[i][1], g[j][1])
        if lo < hi:
            val = f[i][2] * g[j][2]
            if merge and out and out[-1][1] == lo and out[-1][2] == val:
                out[-1][1] = hi
            else:
                out.append([lo, hi, val])
        fi_end, gj_end = f[i][1], g[j][1]
        if fi_end == gj_end:
            i += 1
            j += 1
        elif fi_end < gj_end:
            i += 1
        else:
            j += 1
    return out


def indicator(f):
    """Existence indicator: replace every non-zero count value by 1."""
    out = []
    for lo, hi, v in f:
        if out and out[-1][1] == lo:
            out[-1][1] = hi
        else:
            out.append([lo, hi, 1])
    return out


def indicator_diff(old, new):
    """Signed indicator delta ``1[new] - 1[old]`` as a segment function."""
    return seg_add(indicator(new), seg_negate(indicator(old)))


def cut(f, presence):
    """Keep the parts of ``f`` whose time points are outside ``presence``.

    Both inputs are segment functions; only the support of ``presence``
    matters.  The retained segments keep their original values.  This is
    how a negated literal removes the time points where its tuple exists.
    """
    out = []
    j = 0
    for lo, hi, val in f:
        cur = lo
        k = j
        while k < len(presence) and presence[k][0] < hi:
            s, e = presence[k][0], presence[k][1]
            if e <= lo:
                k += 1
                continue
            if s > cur:
                out.append([cur, min(s, hi), val])
            cur = max(cur, e)
            if cur >= hi:
                break
            k += 1
        if cur < hi:
            out.append([cur, hi, val])
    merged = []
    for lo, hi, val in out:
        if merged and merged[-1][1] == lo and merged[-1][2] == val:
            merged[-1][1] = hi
        else:
            merged.append([lo, hi, val])
    return merged


def has_negative(f):
    """True if any segment of the function has a negative value."""
    return any(seg[2] < 0 for seg in f)


def is_valid(f):
    """Structural validation used while developing and for assertions."""
    prev_end = None
    for seg in f:
        lo, hi, v = seg
        if not (isinstance(lo, int) and isinstance(hi, int)
                and isinstance(v, int)):
            return False
        if lo >= hi or v == 0:
            return False
        if prev_end is not None and lo < prev_end:
            return False
        prev_end = hi
    return True
