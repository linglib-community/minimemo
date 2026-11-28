"""Run minimemo on the models of memo's demos, and check that it gives what memo gives.

    git clone --depth 1 https://github.com/kach/memo memo-src
    python scripts/demos_agree.py memo-src/demo [name ...]

Each demo is run as it is. A model is compared at the first three settings of its parameters
that the demo calls it with. One Lean process runs at a time.
"""
import collections
import inspect
import json
import os
import pathlib
import signal
import sys
import tempfile
import types

os.environ.setdefault("MPLBACKEND", "Agg")
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "tests"))

import jax
import numpy
import memo
from memo import codegen
from memo.core import MemoError
from memo.parse import parse_memo

import test_memo_suite as suite
from test_memo_suite import Test, check

compile_model = codegen.memo
recorded: list[Test] = []
known: dict = {}
scope: dict = {}


def concrete(xs) -> bool:
    return not any(isinstance(x, jax.core.Tracer) for x in xs)


def memo_(f=None, **kwargs):
    """memo's decorator, which also records the first call of the model with numbers."""
    if f is None:
        return lambda g: memo_(g, **kwargs)
    known[f.__name__] = f
    def install(text):  # memo compiles a model in the module of the model, which is the demo
        exec(text, scope)
        return scope
    kwargs.setdefault("install_module", install)
    compile_model(f, **kwargs)
    compiled = scope[f.__name__]  # memo leaves the model there
    before, seen = dict(known), []

    def model(*args, **kw):
        out = compiled(*args, **kw)
        if len(seen) < 3 and concrete(list(args) + list(kw.values())):
            try:
                params = parse_memo(f)[0].static_parameters
                given = list(args) + [kw[p] for p in params[len(args):] if p in kw]
                key = repr([numpy.asarray(g).tolist() for g in given])
                if len(given) == len(args) + len(kw) and key not in seen:
                    seen.append(key)
                    recorded.append(Test(f, dict(known) | before, dict(scope), "pass", out,
                                         tuple(given)))
            except Exception:
                pass
        return out
    model.__dict__.update(getattr(compiled, "__dict__", {}))
    model.__name__ = f.__name__
    return model


def source(path: pathlib.Path) -> str:
    if path.suffix == ".py":
        return path.read_text()
    lines = []
    for cell in json.loads(path.read_text())["cells"]:
        if cell["cell_type"] == "code":
            lines += [l for l in "".join(cell["source"]).split("\n")
                      if not l.lstrip().startswith(("%", "!"))]
    return "\n".join(lines)


def timeout(*_):
    raise TimeoutError


def main() -> int:
    folder = pathlib.Path(sys.argv[1]).resolve()
    only = sys.argv[2:]
    memo.memo = memo_
    counts, reasons, n = collections.Counter(), collections.Counter(), 0
    for path in sorted(list(folder.glob("*.py")) + list(folder.glob("*.ipynb"))):
        if path.name == "test.py" or (only and not any(o in path.name for o in only)):
            continue
        recorded.clear(); known.clear(); scope.clear()
        scope.update({"__name__": "__main__", "__file__": ""})
        signal.signal(signal.SIGALRM, timeout)
        signal.alarm(240)
        try:
            os.chdir(folder)
            script = pathlib.Path(tempfile.mkdtemp()) / (path.stem.replace("-", "_") + ".py")
            script.write_text(source(path))
            exec(compile(script.read_text(), str(script), "exec"), scope)
        except BaseException as e:  # a demo may need data or packages that are not here
            stopped = f"  [stopped: {type(e).__name__}: {str(e)[:60]}]"
        else:
            stopped = ""
        finally:
            signal.alarm(0)
        os.chdir(pathlib.Path(__file__).resolve().parent.parent)
        line = []
        for t in list(recorded):
            n += 1
            verdict, why = check(5000 + n, t)
            counts[verdict] += 1
            if verdict == "skipped":
                reasons[why] += 1
            shown = tuple(round(float(a), 3) if numpy.ndim(a) == 0 else "array" for a in t.args)
            line.append(f"{t.f.__name__}{shown}: {verdict}"
                        + (f" ({why[:60]})" if why and verdict != "ok" else ""))
        print(f"{path.name[:34]:34} " + ("; ".join(line) if line else "no model was called")
              + stopped, flush=True)
    compared = counts["ok"] + counts["differs"]
    print(f"\n{counts['ok']} of {compared} models agree; {counts['skipped']} are outside minimemo")
    for why, k in reasons.most_common():
        print(f"{k:4}  {why}")
    return 1 if counts["differs"] else 0


if __name__ == "__main__":
    sys.exit(main())
