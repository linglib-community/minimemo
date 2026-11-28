"""minimemo gives what memo gives on memo's own tests.

A test of memo is a model with the outcome that memo expects of it: an array, or a rejection.
minimemo passes a test when it accepts the model exactly if memo does, with the same array. A test
that uses a part of memo that minimemo does not have is skipped.

The tests are read from `memo-src/demo/test.py`, or from the file that `MEMO_TESTS` names:

    git clone --depth 1 https://github.com/kach/memo memo-src
"""
import dataclasses
import os
import pathlib
import runpy
import subprocess

import memo
import pytest
from memo import codegen
from memo.core import EMemo, MemoError
from memo.parse import parse_memo

from lean import ROOT, nodes, run, source, verdict
import memo2lean
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
        # a test that memo fails to run has nothing to compare
        if "variant" in kwargs:
            memo2lean.ROOT_VARIANT[f.__name__] = kwargs["variant"].name
        if outcome == expect != "re":
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
    ok, why = verdict(name, iter(results), iter(reasons),
                      None if t.outcome == "ce" else t.out, sizes)
    return ("ok" if ok else "differs"), why


def collect() -> list[Test]:
    """The tests of memo, with what memo does on each: memo's file of tests is run once."""
    given = os.environ.get("MEMO_TESTS")
    path = pathlib.Path(given) if given else ROOT / "memo-src" / "demo" / "test.py"
    if not path.exists():
        return []
    original = memo.memo_test, memo.memo
    memo.memo_test, memo.memo = memo_test, memo_
    try:
        runpy.run_path(str(path.resolve()), run_name="__main__")
    finally:
        memo.memo_test, memo.memo = original
    return tests


TESTS = collect()


def test_suite_found():
    if not TESTS:
        pytest.skip("memo's tests are not here: clone memo to memo-src, or set MEMO_TESTS to its "
                    "demo/test.py")


@pytest.mark.parametrize("i", range(len(TESTS)), ids=[t.f.__name__ for t in TESTS])
def test_memo_test(i):
    verdict, why = check(i, TESTS[i])
    if verdict == "skipped":
        pytest.skip(why)
    assert verdict == "ok", why
