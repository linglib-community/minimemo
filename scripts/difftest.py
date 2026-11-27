"""Check that memo and minimemo give the same arrays on the example models.

    python scripts/difftest.py [module]
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
            if ps:
                lean += [f"def {ident(f.__name__ + '_ref')}{binder} : ℚ :=",
                         f"  Model.ref dom {m} [{', '.join(args.split())}]", ""]
            else:  # the array is computed once
                axes = [s.domain for s in parsed[f.__name__][1] if isinstance(s, SForAll)]
                at = "0"
                for i, d in enumerate(axes):
                    at = f"({at}) * {len(values[d])} + (dom .{d}).index a{i}"
                lean += [f"def {ident(f.__name__ + '_table')} : Array ℚ :=",
                         f"  ((Model.entries dom {m}).getD []).toArray",
                         f"def {ident(f.__name__ + '_ref')}{binder} : ℚ :=",
                         f"  {ident(f.__name__ + '_table')}.getD ({at}) 0", ""]
    args_of = getattr(examples, "ARGS", {})
    for f in raw:
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        lean.append(f"#eval Model.entries dom {m}")
    lean.append('#eval "core"')
    for f in raw:
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        lean.append(f"#eval if Core.Model.covered {m} then some (Core.Model.entries dom {m}) else none")
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text("\n".join(lean) + "\n")

    run = subprocess.run(["lake", "env", "lean", str(OUT)], cwd=ROOT, capture_output=True, text=True)
    if run.returncode != 0:
        print(run.stdout + run.stderr)
        return 1
    first, _, second = run.stdout.partition('"core"')
    results = re.findall(r"some\s*\[(.*?)\]|(none)", first, re.S)
    # the second implementation: its entries, "some none" if it rejects, "none" if not covered
    core = re.findall(r"some\s*\(some\s*\[(.*?)\]\)|(some none)|(none)", second, re.S)

    scope = vars(examples)
    scope["memo"] = memo
    failed = covered = core_failed = 0
    for f, (entries, none), (core_entries, core_none, core_skip) in zip(raw, results, core, strict=True):
        if not core_skip:
            covered += 1
            same = (bool(core_none) and bool(none)) or (
                bool(core_entries) and core_entries.split() == entries.split())
            core_failed += not same
            if not same:
                print(f"FAIL {f.__name__}  (the two implementations differ)")
                if "-v" in sys.argv:
                    print("   semantics:", entries or "none")
                    print("   core:     ", core_entries or "none")
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
            print(f"{'ok  ' if ok else 'FAIL'} {f.__name__}  (rejected)")
            continue
        want = numpy.broadcast_to(numpy.asarray(out), sizes).ravel()
        if False:
            ok = False
        else:
            got = [float(Fraction(*map(int, e.replace(" ", "").split("/")))) for e in entries.split(",")]
            ok = len(got) == len(want) and all(abs(g - w) < 1e-5 for g, w in zip(got, want))
        failed += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {f.__name__}")
        if not ok and "-v" in sys.argv:
            print("   memo:", [round(float(w), 5) for w in want])
            print("   lean:", [round(g, 5) for g in got])
    print(f"{len(raw) - failed} of {len(raw)} models agree")
    print(f"{covered - core_failed} of {covered} models agree in the second implementation "
          f"({len(raw) - covered} not covered)")
    return 1 if failed or core_failed else 0


if __name__ == "__main__":
    sys.exit(main())
