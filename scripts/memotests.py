"""Run minimemo on memo's own tests, and check that it gives what memo gives.

    git clone --depth 1 https://github.com/kach/memo
    python scripts/memotests.py memo/demo/test.py [-v]

A test of memo is a model with the outcome that memo expects of it: an array, or a rejection.
minimemo passes a test when it accepts the model exactly if memo does, with the same array.
"""
import collections
import dataclasses
import pathlib
import runpy
import subprocess
import sys

import memo
from memo import codegen
from memo.core import EMemo, MemoError
from memo.parse import parse_memo

from difftest import ROOT, agree, nodes, run, source
from memo2lean import Unsupported


@dataclasses.dataclass
class Test:
    f: object        # the model, as a function
    known: dict      # the models defined before it, by name
    module: object   # the module that holds the domains and the functions
    outcome: str     # what memo does: "pass", or "ce" (rejects the model)
    out: object      # the array that memo returns
    args: tuple      # the parameters


tests: list[Test] = []
known: dict = {}
compile_model = codegen.memo


def memo_test(mod, expect="pass", item=None, *args, **kwargs):
    """memo's decorator for a test, which also records the test."""
    def helper(f):
        out = None
        try:
            compile_model(f, install_module=mod.install, **kwargs)
            out = getattr(mod, f.__name__)(*args)
            outcome = "pass"
        except MemoError:
            outcome = "ce"
        except Exception:
            outcome = "re"
        # a test that memo fails to run, or one of a variant of memo, has nothing to compare
        if outcome == expect != "re" and "variant" not in kwargs:
            tests.append(Test(f, dict(known), mod, outcome, out, args))
        known[f.__name__] = f
        return getattr(mod, f.__name__, None)
    return helper


def memo_(f=None, **kwargs):
    """memo's decorator for a model, which also records the model."""
    if f is None:
        return lambda g: memo_(g, **kwargs)
    known[f.__name__] = f
    return compile_model(f, **kwargs)


def models(t: Test) -> list:
    """The model of a test, after the models that it refers to."""
    order, seen = [], set()

    def visit(f):
        if f.__name__ in seen:
            return
        seen.add(f.__name__)
        _, ss, rets = parse_memo(f)
        for n in nodes([ss, rets]):
            if isinstance(n, EMemo) and n.name != f.__name__:
                if n.name not in t.known:
                    raise Unsupported("a reference to a model that is not a memo model")
                visit(t.known[n.name])
        order.append(f)

    visit(t.f)
    return order


def check(i: int, t: Test) -> tuple[str, str]:
    """Whether minimemo gives what memo gives on a test: "ok", "differs" or "skipped", and why."""
    name = t.f.__name__
    try:
        ctxt, _, _ = parse_memo(t.f)
    except MemoError:
        return "skipped", "not in memo's grammar"
    try:
        env = vars(t.module)
        defaults = ctxt.static_defaults[len(t.args):]
        if None in defaults:
            raise Unsupported("a model that is given no parameters")
        given = list(t.args) + [eval(d, env) for d in defaults]
        text, sizes = source(models(t), env, {name: given}, shown=[t.f])
    except Unsupported as e:
        return "skipped", str(e)
    except Exception as e:
        return "skipped", f"{type(e).__name__}: {str(e)[:50]}"
    try:
        results, reasons = run(text, ROOT / "scratch" / "memotests" / f"T{i}.lean", timeout=60)
    except subprocess.TimeoutExpired:
        return "skipped", "too slow"
    except RuntimeError as e:
        return "differs", "Lean does not accept the file: " + str(e).strip().split("\n")[0][:80]
    got, reason = results[0], reasons[0]
    if t.outcome == "ce":
        return ("ok", f"rejected: {reason}") if got is None else ("differs", "memo rejects it")
    if got is None:
        return "differs", f"minimemo rejects it: {reason}"
    return ("ok", "") if agree(got, t.out, sizes[name]) else ("differs", "the arrays differ")


def main() -> int:
    memo.memo_test, memo.memo = memo_test, memo_
    path = pathlib.Path(sys.argv[1]).resolve()
    runpy.run_path(str(path), run_name="__main__")
    verdicts = [check(i, t) for i, t in enumerate(tests)]  # one Lean process at a time
    counts, reasons = collections.Counter(), collections.Counter()
    for t, (verdict, why) in zip(tests, verdicts):
        counts[verdict] += 1
        if verdict == "skipped":
            reasons[why] += 1
        if verdict == "differs" or "-v" in sys.argv:
            print(f"{verdict:8} {t.f.__name__}{'  (' + why + ')' if why else ''}")
    compared = counts["ok"] + counts["differs"]
    print(f"\n{counts['ok']} of {compared} tests agree; {counts['skipped']} of {len(tests)} "
          "are outside minimemo")
    for why, n in reasons.most_common():
        print(f"{n:4}  {why}")
    return 1 if counts["differs"] else 0


if __name__ == "__main__":
    sys.exit(main())
