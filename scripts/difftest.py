"""Check that memo and minimemo give the same arrays on the example models.

    python scripts/difftest.py [module] [-v] [--core]

Both implementations in Lean are compared with memo and with each other. With `--core`, only the
programs on tables are run.
"""
import dataclasses
import itertools
import pathlib
import re
import subprocess
import sys
from fractions import Fraction

import numpy
from memo import memo
from memo.core import MemoError
from memo.core import (EChoice, EFFI, EMemo, EWith, SChoose, SForAll, SKnows, SShow, SSnapshot,
                       SWith)
from memo.parse import parse_memo

import importlib

examples = importlib.import_module(next((a for a in sys.argv[1:] if not a.startswith('-')), 'examples'))
import memo2lean
from memo2lean import ident, model

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "scratch" / "difftest.lean"


def nodes(x):
    """Every syntax node inside `x`."""
    if dataclasses.is_dataclass(x) and not isinstance(x, type):
        yield x
        for f in dataclasses.fields(x):
            yield from nodes(getattr(x, f.name))
    elif isinstance(x, (list, tuple)):
        for y in x:
            yield from nodes(y)
    elif isinstance(x, dict):
        for y in x.values():
            yield from nodes(y)


def rat(x) -> str:
    q = Fraction(float(x))
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator} / {q.denominator})"


def choice_name(e):
    match e:
        case EChoice(id=name) | EWith(expr=EChoice(id=name)):
            return name
    raise SystemExit("a foreign function is applied to something other than a choice")


def main() -> int:
    raw = list(examples.MODELS)
    parsed = {f.__name__: parse_memo(f) for f in raw}
    agents, names, domain_of, calls, referenced = [], [], {}, {}, []

    def add(xs, x):
        if x != "self" and x not in xs:
            xs.append(x)

    for _, ss, rets in parsed.values():
        for n in nodes([ss, rets]):
            match n:
                case SForAll(id=x, domain=d):
                    add(names, x); domain_of.setdefault(x, set()).add(d)
                case SChoose(who=a, choices=cs):
                    add(agents, a)
                    for x, d in cs:
                        add(names, x); domain_of.setdefault(x, set()).add(d)
                case SWith(who=a) | EWith(who=a):
                    add(agents, a)
                case SShow(who=a, target_who=b, source_who=g) :
                    add(agents, a); add(agents, b); add(agents, g)
                case SSnapshot(who=a, alias=b):
                    add(agents, a); add(agents, b)
                case SKnows(who=a, source_who=g):
                    add(agents, a); add(agents, g)
                case EChoice(id=x):
                    add(names, x)
                case EMemo(name=m, ids=ids):
                    add(referenced, m)
                    for _, who, _ in ids:
                        add(agents, who)
    for _, ss, rets in parsed.values():
        for n in nodes([ss, rets]):
            if isinstance(n, EFFI):
                slots = calls.setdefault(n.name, [set() for _ in n.args])
                for slot, arg in zip(slots, n.args):
                    slot |= domain_of[choice_name(arg)]
    domains = sorted({d for ds in domain_of.values() for d in ds})
    values = {d: [int(v) for v in getattr(examples, d)] for d in domains}
    for name, slots in calls.items():
        point = [values[sorted(slot)[0]][0] for slot in slots]
        if numpy.asarray(getattr(examples, name)(*point)).dtype == bool:
            memo2lean.BOOLEAN_FUNCTIONS.add(name)

    lean = ["import Minimemo.Semantics", "import Minimemo.Core.Compile",
            "import Mathlib.Algebra.Order.Field.Rat", "",
            "open Memo", "open scoped Memo", "",
            f"inductive Agent | {' | '.join(map(ident, agents))} deriving DecidableEq",
            f"inductive Name | {' | '.join(map(ident, names))} deriving DecidableEq",
            f"inductive Dom | {' | '.join(domains)} deriving DecidableEq", "",
            "def dom : Dom → Domain ℚ"]
    for d in domains:
        vs = ", ".join(rat(v) for v in values[d])
        lean.append(f"  | .{d} => ⟨{len(values[d])}, fun j ↦ ([{vs}] : List ℚ).getD j 0⟩")
    lean += ["", "def eq (a b : ℚ) : ℚ := if a = b then 1 else 0",
             "def ne (a b : ℚ) : ℚ := if a = b then 0 else 1",
             "def lt (a b : ℚ) : ℚ := if a < b then 1 else 0",
             "def le (a b : ℚ) : ℚ := if a ≤ b then 1 else 0",
             "def gt (a b : ℚ) : ℚ := if a > b then 1 else 0",
             "def ge (a b : ℚ) : ℚ := if a ≥ b then 1 else 0",
             "def both (a b : ℚ) : ℚ := if a ≠ 0 ∧ b ≠ 0 then 1 else 0",
             "def either (a b : ℚ) : ℚ := if a ≠ 0 ∨ b ≠ 0 then 1 else 0",
             "def cond3 (c a b : ℚ) : ℚ := if c ≠ 0 then a else b",
             "def truthy (a : ℚ) : ℚ := if a ≠ 0 then 1 else 0", ""]
    for name, slots in calls.items():
        f = getattr(examples, name)
        points = itertools.product(*[sorted({v for d in slot for v in values[d]}) for slot in slots])
        rows = ", ".join(f"([{', '.join(rat(v) for v in p)}], {rat(f(*p))})" for p in points)
        args = " ".join(f"a{i}" for i in range(len(slots)))
        lean += [f"def {ident(name)} ({args} : ℚ) : ℚ :=",
                 f"  (List.lookup [{', '.join(args.split())}] "
                 f"([{rows}] : List (List ℚ × ℚ))).getD 0", ""]
    for f in raw:
        lean.append(model(f))
        if f.__name__ in referenced:
            k = sum(isinstance(s, SForAll) for s in parsed[f.__name__][1])
            args = " ".join(f"a{i}" for i in range(k))
            ps = " ".join(map(ident, parsed[f.__name__][0].static_parameters))
            binder = f" ({ps} {args} : ℚ)" if ps else f" ({args} : ℚ)"
            m = f"({ident(f.__name__)} {ps})" if ps else ident(f.__name__)
            axes = [s.domain for s in parsed[f.__name__][1] if isinstance(s, SForAll)]
            at = "0"
            for i, d in enumerate(axes):
                at = f"({at}) * {len(values[d])} + (dom .{d}).index a{i}"
            if ps:
                lean += [f"def {ident(f.__name__ + '_ref')}{binder} : ℚ :=",
                         f"  ((Core.Model.entries dom {m}).getD []).getD ({at}) 0", ""]
            else:  # the array is computed once
                lean += [f"def {ident(f.__name__ + '_table')} : Array ℚ :=",
                         f"  ((Core.Model.entries dom {m}).getD []).toArray",
                         f"def {ident(f.__name__ + '_ref')}{binder} : ℚ :=",
                         f"  {ident(f.__name__ + '_table')}.getD ({at}) 0", ""]
    args_of = getattr(examples, "ARGS", {})
    for f in raw:
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        if "--core" not in sys.argv:
            lean.append(f"#eval Model.entries dom {m}")
    lean.append('#eval "core"')
    for f in raw:
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        lean.append(f"#eval Core.Model.entries dom {m}")
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text("\n".join(lean) + "\n")

    run = subprocess.run(["lake", "env", "lean", str(OUT)], cwd=ROOT, capture_output=True, text=True)
    if run.returncode != 0:
        print(run.stdout + run.stderr)
        return 1
    first, _, second = run.stdout.partition('"core"')
    pattern = r"some\s*\[(.*?)\]|(none)"
    core = re.findall(pattern, second, re.S)
    both = "--core" not in sys.argv
    semantics = re.findall(pattern, first, re.S) if both else [None] * len(raw)

    def agrees(result, want):
        """Whether a result in Lean, entries or a rejection, is what memo gives."""
        entries, none = result
        if none or want is None:
            return bool(none) and want is None
        got = [float(Fraction(*map(int, e.replace(" ", "").split("/")))) for e in entries.split(",")]
        # memo adds in single precision, and a model with many choices adds many numbers
        return len(got) == len(want) and all(
            abs(g - w) < 1e-4 * max(1, abs(w)) for g, w in zip(got, want))

    scope = vars(examples)
    scope["memo"] = memo
    failed = {"semantics": 0, "core": 0, "each other": 0}
    for f, sem, cor in zip(raw, semantics, core, strict=True):
        # memo compiles a model in the scope of its caller, which has to be the module of the model
        sizes = [len(values[s.domain]) for s in parsed[f.__name__][1] if isinstance(s, SForAll)]
        try:
            exec(f"{f.__name__} = memo({f.__name__})", scope)
            out = scope[f.__name__](*args_of.get(f.__name__, ()))
            want = numpy.broadcast_to(numpy.asarray(out), sizes).ravel()
        except MemoError:
            want = None
        wrong = [] if agrees(cor, want) else ["core"]
        if both and not agrees(sem, want):
            wrong.append("semantics")
        if both and (sem[0].split(), sem[1]) != (cor[0].split(), cor[1]):
            wrong.append("each other")
        for w in wrong:
            failed[w] += 1
        note = "  (rejected)" if want is None else ""
        print(f"{'FAIL' if wrong else 'ok  '} {f.__name__}{note}{'  ' + ', '.join(wrong) if wrong else ''}")
        if wrong and "-v" in sys.argv:
            print("   memo:     ", None if want is None else [round(float(w), 5) for w in want])
            if both:
                print("   semantics:", sem[0] or "none")
            print("   core:     ", cor[0] or "none")
    n = len(raw)
    if both:
        print(f"{n - failed['semantics']} of {n} models agree with memo in the semantics")
    print(f"{n - failed['core']} of {n} models agree with memo as programs on tables")
    if both:
        print(f"{n - failed['each other']} of {n} models agree in the two")
    return 1 if any(failed.values()) else 0


if __name__ == "__main__":
    sys.exit(main())
