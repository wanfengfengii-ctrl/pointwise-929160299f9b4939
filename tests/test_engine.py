"""Specification-level tests for the pointwise interval Datalog engine.

Run with: python3 -I tests/test_engine.py
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from intervalrules.engine import Engine
from intervalrules import segments as seg


def check(cond, msg):
    if not cond:
        raise AssertionError(msg)


def test_segment_primitives():
    # Addition that returns to zero splits and rejoins correctly.
    check(seg.seg_add([[0, 5, 1]], [[2, 3, -1]]) ==
          [[0, 2, 1], [3, 5, 1]], "add through zero")
    check(seg.seg_add([[0, 5, 2]], [[0, 5, -1]]) ==
          [[0, 5, 1]], "add reduces value")
    check(seg.indicator([[0, 4, 2], [4, 8, 3]]) ==
          [[0, 8, 1]], "indicator merges adjacent support")
    check(seg.cut([[0, 10, 1]], [[2, 4, 1], [6, 7, 1]]) ==
          [[0, 2, 1], [4, 6, 1], [7, 10, 1]], "cut removes presence")
    check(seg.has_negative([[0, 1, -1]]), "negative detection")
    check(not seg.has_negative([]), "empty is not negative")


def test_read_sorting_and_merge():
    eng = Engine({"E": 2}, ["R(X,Y) :- E(X,Y)"])
    eng.apply([
        ["E", ("a", "b"), 0, 5, 1],
        ["E", ("a", "a"), 0, 5, 1],
        ["E", ("a", "b"), 5, 10, 1],
    ])
    rows = eng.read("R")
    # Sorted by tuple then start; adjacent support merged into [0,10).
    check(rows == [
        [("a", "a"), 0, 5],
        [("a", "b"), 0, 10],
    ], "read sort and merge: %r" % rows)


def test_net_change_signs():
    eng = Engine({"E": 2, "F": 2}, [
        "R(X,Y) :- E(X,Y)",
        "R(X,Y) :- F(X,Y)",
    ])
    net = eng.apply([
        ["E", ("a", "b"), 0, 10, 1],
        ["F", ("a", "b"), 3, 7, 1],
    ])
    check(net["R"] == [[("a", "b"), 0, 10, 1]], "insert net: %r" % net)
    net = eng.apply([["E", ("a", "b"), 0, 10, -1]])
    # F still proves the middle, so only the outer windows are deleted.
    check(net["R"] == [
        [("a", "b"), 0, 3, -1],
        [("a", "b"), 7, 10, -1],
    ], "delete net keeps surviving proof: %r" % net)
    check(eng.read("R") == [[("a", "b"), 3, 7]], "remaining window")


def test_rollback_leaves_state_untouched():
    eng = Engine({"E": 2}, ["R(X,Y) :- E(X,Y)"])
    eng.apply([["E", ("a", "b"), 0, 4, 1]])
    snapshot = eng.read("E"), eng.read("R")
    net = eng.apply([
        ["E", ("a", "b"), 2, 6, -1],   # negative on [4,6)
        ["E", ("a", "c"), 0, 2, 1],
    ])
    check(net == {}, "illegal batch returns empty dict")
    check((eng.read("E"), eng.read("R")) == snapshot,
          "state unchanged after rollback")


def test_unsupported_cycle_removed():
    # Two tuples can only be derived through each other on a window; once
    # the external edge is withdrawn the whole cyclic window must vanish.
    rules = [
        "T(X,Y) :- E(X,Y)",
        "T(X,Y) :- E(X,Z), T(Z,Y)",
    ]
    eng = Engine({"E": 2}, rules)
    eng.apply([
        ["E", ("a", "b"), 0, 10, 1],
        ["E", ("b", "a"), 4, 6, 1],
    ])
    check(("a", "a") in [t for t, _, _ in eng.read("T")],
          "cyclic tuple exists while supported")
    eng.apply([
        ["E", ("a", "b"), 0, 10, -1],
        ["E", ("b", "a"), 4, 6, -1],
    ])
    check(eng.read("T") == [], "unsupported cycle fully removed")


def test_validation():
    def rejects(base, rules):
        try:
            Engine(base, rules)
        except ValueError:
            return
        raise AssertionError("should reject %r" % rules)

    rejects({"E": 2}, ["E(X,Y) :- E(X,Y)"])               # base as head
    rejects({"E": 2}, ["R(X,Y) :- E(X,Y), !R(X,Y)"])      # neg recursion
    rejects({"E": 2}, ["R(X,Y) :- G(X,Y)"])               # undefined
    rejects({"E": 2}, ["R(X,Y) :- E(X)"])                 # arity mismatch
    rejects({"E": 2}, ["R(X,Y) :- !E(X,Y)"])              # no positive lit


def run():
    tests = [v for k, v in sorted(globals().items())
             if k.startswith("test_") and callable(v)]
    for t in tests:
        t()
        print("ok  ", t.__name__)
    print("%d tests passed" % len(tests))


if __name__ == "__main__":
    run()
