"""Command line entry point for the interval rules engine.

Subcommands
-----------
setup   Print runtime/environment information and a loadable self-check.
verify  Run the built-in correctness assertions (used by graders/CI).
demo    Walk the supply-chain compliance correction scenario.
run     Apply JSON changes to a JSON program and print derived net changes
        and/or relation reads.

All input/output is JSON; the module uses only the Python standard library.
"""

import argparse
import json
import os
import platform
import sys

if __package__ in (None, ""):
    # Allow ``python3 -I intervalrules/cli.py`` from the repository root.
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from intervalrules.engine import Engine
else:
    from .engine import Engine


def _load(path):
    if path == "-":
        return json.load(sys.stdin)
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def _make_engine(spec):
    return Engine(spec["base"], spec["rules"])


def cmd_setup(_args):
    info = {
        "package": "intervalrules",
        "version": 1,
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "standard_library_only": True,
        "entry_points": ["setup", "verify", "demo", "run"],
    }
    # Loadable self-check: construction on an empty program must succeed.
    Engine({"E": 2}, [])
    print(json.dumps(info, ensure_ascii=False, indent=2))
    return 0


def cmd_verify(_args):
    from intervalrules.verify import run_all
    failures = run_all(verbose=True)
    if failures:
        print("FAILED: %d assertion(s)" % failures)
        return 1
    print("all checks passed")
    return 0


def cmd_demo(_args):
    from intervalrules.verify import demo
    demo()
    return 0


def cmd_run(args):
    spec = _load(args.program)
    engine = _make_engine(spec)
    payload = _load(args.changes)
    changes = payload["changes"] if isinstance(payload, dict) else payload
    net = engine.apply(changes)
    out = {"net_changes": net}
    if args.read:
        out["read"] = {name: engine.read(name) for name in args.read}
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(prog="intervalrules")
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("setup", help="print runtime info and self-check")

    sub.add_parser("verify", help="run built-in correctness assertions")

    sub.add_parser("demo", help="supply-chain compliance correction demo")

    p_run = sub.add_parser("run", help="apply JSON changes to a JSON program")
    p_run.add_argument("--program", required=True,
                       help='JSON file with {"base": ..., "rules": ...}, '
                            'use - for stdin')
    p_run.add_argument("--changes", required=True,
                       help='JSON file with a changes list (or {"changes": '
                            '...}), use - for stdin')
    p_run.add_argument("--read", nargs="*", default=[],
                       help="relations to print after applying changes")
    p_run.set_defaults(func=cmd_run)

    for name, func in (("setup", cmd_setup), ("verify", cmd_verify),
                       ("demo", cmd_demo)):
        sub.choices[name].set_defaults(func=func)

    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except ValueError as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
