"""Report which models in memo's demos minimemo can translate.

    git clone --depth 1 https://github.com/kach/memo
    python scripts/demos.py memo/demo
"""
import collections
import json
import os
import pathlib
import signal
import sys
import tempfile
import types

os.environ.setdefault("MPLBACKEND", "Agg")

from memo import codegen

import memo2lean
from memo.parse import parse_memo
from memo2lean import Unsupported, model

seen = []
original = codegen.parse_memo


def recording(f):
    seen.append(f)
    return original(f)


codegen.parse_memo = recording


def source(path: pathlib.Path) -> str:
    if path.suffix == ".py":
        return path.read_text()
    cells = json.loads(path.read_text())["cells"]
    lines = []
    for cell in cells:
        if cell["cell_type"] == "code":
            lines += [l for l in "".join(cell["source"]).split("\n") if not l.lstrip().startswith(("%", "!"))]
    return "\n".join(lines)


def timeout(*_):
    raise TimeoutError


def main() -> None:
    folder = pathlib.Path(sys.argv[1])
    reasons = collections.Counter()
    total = translated = 0
    for path in sorted(list(folder.glob("*.py")) + list(folder.glob("*.ipynb"))):
        seen.clear()
        note = ""
        signal.signal(signal.SIGALRM, timeout)
        signal.alarm(180)
        scope = {"__name__": "__main__", "__file__": ""}
        try:
            os.chdir(folder)
            # memo reads a model's source back from its file, so a notebook's code goes in a file
            script = pathlib.Path(tempfile.mkdtemp()) / (path.stem.replace("-", "_") + ".py")
            script.write_text(source(path))
            exec(compile(script.read_text(), str(script), "exec"), scope)
        except BaseException as e:  # a demo may need data or packages that are not here
            note = f"  (stopped: {type(e).__name__})"
        finally:
            signal.alarm(0)
        # a Python expression in braces is read in the module of the model
        made = [vars(v) for v in scope.values() if isinstance(v, types.ModuleType)
                and getattr(v, "__file__", None) is None]
        memo2lean.INLINE_ENV = {k: v for d in made + [scope] for k, v in d.items()}
        memo2lean.SIGNATURES = {}
        for f in seen:
            try:
                ctxt = parse_memo(f)[0]
                memo2lean.SIGNATURES[f.__name__] = (list(ctxt.static_parameters),
                                                   list(ctxt.static_defaults))
            except Exception:
                pass
        ok, bad = 0, collections.Counter()
        for f in seen:
            try:
                model(f)
                ok += 1
            except Unsupported as e:
                bad[str(e)] += 1
            except Exception as e:
                bad[f"{type(e).__name__}: {str(e)[:40]}"] += 1
        total += len(seen)
        translated += ok
        reasons.update(bad)
        why = ", ".join(f"{k} x{v}" for k, v in bad.most_common(4))
        print(f"{path.name[:32]:32} {ok:3}/{len(seen):<3} {why}{note}")
    print(f"\n{translated} of {total} models translate")
    for k, v in reasons.most_common():
        print(f"{v:4}  {k}")


if __name__ == "__main__":
    main()
