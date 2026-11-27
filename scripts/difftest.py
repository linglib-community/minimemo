"""Check that memo and minimemo give the same arrays on the example models.

    python scripts/difftest.py [module] [-v]
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

    def axes_of(name):
        return [s.domain for s in parsed[name][1] if isinstance(s, SForAll)]

    # the outside functions: those of the models, and a reference to each model that is referenced
    fns = [f"  | {ident(name)} : Fn {len(slots)}" for name, slots in calls.items()]
    for name in referenced:
        ps = " ".join(map(ident, parsed[name][0].static_parameters))
        fns.append(f"  | {ident(name + '_ref')}{f' ({ps} : ℚ)' if ps else ''} : Fn {len(axes_of(name))}")
    lean = ["import Minimemo.Model", "import Mathlib.Algebra.Order.Field.Rat", "",
            "open Memo", "open scoped Memo", "",
            f"inductive Agent | {' | '.join(map(ident, agents))} deriving DecidableEq, Repr",
            f"inductive Name | {' | '.join(map(ident, names))} deriving DecidableEq, Repr",
            f"inductive Dom | {' | '.join(domains)} deriving DecidableEq",
            "inductive Fn : ℕ → Type", *fns, "",
            "def dom : Dom → Domain ℚ"]
    for d in domains:
        vs = ", ".join(rat(v) for v in values[d])
        lean.append(f"  | .{d} => ⟨{len(values[d])}, fun j ↦ ([{vs}] : List ℚ).getD j 0⟩")
    lean.append("")
    for name, slots in calls.items():
        f = getattr(examples, name)
        points = itertools.product(*[sorted({v for d in slot for v in values[d]}) for slot in slots])
        rows = ", ".join(f"([{', '.join(rat(v) for v in p)}], {rat(f(*p))})" for p in points)
        args = " ".join(f"a{i}" for i in range(len(slots)))
        lean += [f"def {ident(name)} ({args} : ℚ) : ℚ :=",
                 f"  (List.lookup [{', '.join(args.split())}] "
                 f"([{rows}] : List (List ℚ × ℚ))).getD 0", ""]
    lean += [model(f) for f in raw]
    # the meaning of the outside functions. A reference to a model reads the array of that model,
    # which is computed once for each place where the reference stands. A model may refer to
    # itself with other parameters, as in memo, so the meaning is defined by recursion.
    if calls or referenced:
        lean.append("partial def call : {k : ℕ} → Fn k → (Fin k → ℚ) → ℚ")
        for name, slots in calls.items():
            applied = " ".join(f"(v {i})" for i in range(len(slots)))
            lean.append(f"  | _, .{ident(name)} => fun v ↦ {ident(name)} {applied}")
        for name in referenced:
            ps = " ".join(map(ident, parsed[name][0].static_parameters))
            m = f"({ident(name)} {ps})" if ps else ident(name)
            at = "0"
            for i, d in enumerate(axes_of(name)):
                at = f"({at}) * {len(values[d])} + (dom .{d}).index (v {i})"
            lean += [f"  | _, .{ident(name + '_ref')}{' ' + ps if ps else ''} =>",
                     f"    let table := ((Model.entries (.ofField dom call) {m}).getD []).toArray",
                     f"    fun v ↦ table.getD ({at}) 0"]
    else:
        lean.append("def call : {k : ℕ} → Fn k → (Fin k → ℚ) → ℚ := fun f _ ↦ nomatch f")
    lean += ["", "def interp : Interp Dom Fn ℚ := .ofField dom call", ""]
    args_of = getattr(examples, "ARGS", {})
    for f in raw:
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        lean.append(f"#eval Model.entries interp {m}")
    lean.append('#eval "errors"')
    for f in raw:  # why each model is not accepted, if it is not
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        lean.append(f"#eval Model.error {m}")
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text("\n".join(lean) + "\n")

    run = subprocess.run(["lake", "env", "lean", str(OUT)], cwd=ROOT, capture_output=True, text=True)
    if run.returncode != 0:
        print(run.stdout + run.stderr)
        return 1
    arrays, _, errors = run.stdout.partition('"errors"')
    results = re.findall(r"some\s*\[(.*?)\]|(none)", arrays, re.S)
    reasons = [None if line == "none" else
               re.sub(r"\b(Memo\.)?(Error|Agent|Name|Ref)\.", "", line[len("some ("):-1])
               for line in errors.splitlines() if line.startswith(("none", "some"))]

    scope = vars(examples)
    scope["memo"] = memo
    failed = 0
    for f, (entries, none), reason in zip(raw, results, reasons, strict=True):
        # memo compiles a model in the scope of its caller, which has to be the module of the model
        sizes = [len(values[s.domain]) for s in parsed[f.__name__][1] if isinstance(s, SForAll)]
        try:
            exec(f"{f.__name__} = memo({f.__name__})", scope)
            out = scope[f.__name__](*args_of.get(f.__name__, ()))
        except MemoError:
            out = None
        if none or out is None:
            ok = bool(none) and out is None
            failed += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {f.__name__}  (rejected: {reason or 'by memo only'})")
            continue
        want = numpy.broadcast_to(numpy.asarray(out), sizes).ravel()
        got = [float(Fraction(*map(int, e.replace(" ", "").split("/")))) for e in entries.split(",")]
        # memo adds in single precision, and a model with many choices adds many numbers
        ok = len(got) == len(want) and all(
            abs(g - w) < 1e-4 * max(1, abs(w)) for g, w in zip(got, want))
        failed += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {f.__name__}")
        if not ok and "-v" in sys.argv:
            print("   memo:", [round(float(w), 5) for w in want])
            print("   lean:", [round(g, 5) for g in got])
    print(f"{len(raw) - failed} of {len(raw)} models agree")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
