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
from memo.lib import Bool
from memo.core import MemoError
from memo.core import (EChoice, EFFI, EMemo, EOp, EWith, SChoose, SForAll, SKnows, SShow, SSnapshot,
                       SWith)
from memo.parse import parse_memo

import enum
import importlib

import memo2lean
from memo2lean import Unsupported, ident, model

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


def bars(names) -> str:
    """The constructors of an inductive type that may have none."""
    return "".join(f" | {name}" for name in names)


def flt(x) -> str:
    x = float(x)
    if x != x or x in (float("inf"), float("-inf")):
        raise Unsupported("a value that is not a finite number")
    return f"({x!r})" if x < 0 else repr(x)


def choice_name(e):
    match e:
        case EChoice(id=name) | EWith(expr=EChoice(id=name)):
            return name
    raise Unsupported("a function applied to something other than a choice")


def number(v):
    """A value of a domain or of a function, as a Python number."""
    return int(v) if isinstance(v, enum.IntEnum) else numpy.asarray(v).item()


def source(raw, env, args_of, shown=None):
    """The Lean file that computes the arrays of the models `shown` among the models `raw`, with
    the domains and the functions taken from `env`. Returns the file and the sizes of the axes of
    each model shown."""
    parsed = {f.__name__: parse_memo(f) for f in raw}
    shown = raw if shown is None else shown
    memo2lean.BOOLEAN_FUNCTIONS.clear()
    # a model with an exponential has no rational array, and is run in floating point
    outside = sorted({memo2lean.OUTSIDE[n.op] for _, ss, rets in parsed.values()
                      for n in nodes([ss, rets]) if isinstance(n, EOp) and n.op in memo2lean.OUTSIDE})
    K, num = ("Float", flt) if outside else ("ℚ", rat)
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
    env = {"Bool": Bool} | dict(env)  # memo's own domain of the two truth values
    values = {d: [number(v) for v in env[d]] for d in domains}
    # a table has an entry for each joint value of its choices, so large domains are not run
    if any(len(vs) > 64 for vs in values.values()):
        raise Unsupported("a domain with more than 64 values")
    for name, slots in calls.items():
        point = [values[sorted(slot)[0]][0] for slot in slots]
        if numpy.asarray(env[name](*point)).dtype == bool:
            memo2lean.BOOLEAN_FUNCTIONS.add(name)

    def axes_of(name):
        return [s.domain for s in parsed[name][1] if isinstance(s, SForAll)]

    # the outside functions: those of the models, and a reference to each model that is referenced
    fns = [f"  | {ident(name)} : Fn {len(slots)}" for name, slots in calls.items()]
    fns += [f"  | {name} : Fn {2 if name == 'rpow' else 1}" for name in outside]
    for name in referenced:
        ps = " ".join(map(ident, parsed[name][0].static_parameters))
        fns.append(f"  | {ident(name + '_ref')}{f' ({ps} : ℚ)' if ps else ''} : Fn {len(axes_of(name))}")
    lean = ["import Minimemo", "import Mathlib.Algebra.Order.Field.Rat", "",
            "open Memo", "open scoped Memo", "",
            f"inductive Agent{bars(map(ident, agents))} deriving DecidableEq, Repr",
            f"inductive Name{bars(map(ident, names))} deriving DecidableEq, Repr",
            f"inductive Dom{bars(domains)} deriving DecidableEq",
            "inductive Fn : ℕ → Type", *fns, "",
            f"def dom : Dom → Domain {K}" + ("" if domains else " := fun d ↦ nomatch d")]
    for d in domains:
        vs = ", ".join(num(v) for v in values[d])
        lean.append(f"  | .{d} => ⟨{len(values[d])}, fun j ↦ ([{vs}] : List {K}).getD j 0⟩")
    lean.append("")
    for name, slots in calls.items():
        f = env[name]
        columns = [sorted({v for d in slot for v in values[d]}) for slot in slots]
        if numpy.prod([len(c) for c in columns]) > 4096:
            raise Unsupported("a function with too many values to list")
        points = itertools.product(*columns)
        rows = ", ".join(f"([{', '.join(num(v) for v in p)}], {num(number(f(*p)))})" for p in points)
        args = " ".join(f"a{i}" for i in range(len(slots)))
        binder = f" ({args} : {K})" if slots else ""
        lean += [f"def {ident(name)}{binder} : {K} :=",
                 f"  (List.lookup [{', '.join(args.split())}] "
                 f"([{rows}] : List (List {K} × {K}))).getD 0", ""]
    lean += [model(f) for f in raw]
    # the meaning of the outside functions. A reference to a model reads the array of that model,
    # which is computed once for each place where the reference stands. A model may refer to
    # itself with other parameters, as in memo, so the meaning is defined by recursion.
    interp = ".ofFloat" if outside else ".ofField"
    if calls or referenced or outside:
        lean.append(f"partial def call : {{k : ℕ}} → Fn k → (Fin k → {K}) → {K}")
        lean += [f"  | _, .{name} => Exp.float .{name}" for name in outside]
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
                     f"    let table := ((Model.entries ({interp} dom call) {m}).getD []).toArray",
                     f"    fun v ↦ table.getD ({at}) 0"]
    else:
        lean.append(f"def call : {{k : ℕ}} → Fn k → (Fin k → {K}) → {K} := fun f _ ↦ nomatch f")
    lean += ["", f"def interp : Interp Dom Fn {K} := {interp} dom call", ""]
    for f in shown:
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        lean.append(f"#eval Model.entries interp {m}")
    lean.append('#eval "errors"')
    for f in shown:  # why each model is not accepted, if it is not
        given = "".join(f" {rat(a)}" for a in args_of.get(f.__name__, ()))
        m = f"({ident(f.__name__)}{given})" if given else ident(f.__name__)
        lean.append(f"#eval Model.error {m}")
    sizes = {f.__name__: [len(values[d]) for d in axes_of(f.__name__)] for f in shown}
    return "\n".join(lean) + "\n", sizes


def run(text, path=OUT, timeout=None):
    """The arrays and the reasons for rejection that Lean prints for the file `text`: for each
    model shown, the entries of its array or `None`, and the reason or `None`."""
    path.parent.mkdir(exist_ok=True, parents=True)
    path.write_text(text)
    done = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True,
                          text=True, timeout=timeout)
    if done.returncode != 0:
        raise RuntimeError(done.stdout + done.stderr)
    arrays, _, errors = done.stdout.partition('"errors"')
    results = [None if none else
               [float(Fraction(*map(int, e.replace(" ", "").split("/")))) if "/" in e else float(e)
                for e in entries.split(",")]
               for entries, none in re.findall(r"some\s*\[(.*?)\]|(none)", arrays, re.S)]
    reasons = [None if line == "none" else
               re.sub(r"\b(Memo\.)?(Error|Agent|Name|Ref)\.", "", line[len("some ("):-1])
               for line in errors.splitlines() if line.startswith(("none", "some"))]
    return results, reasons


def agree(got, out, sizes) -> bool:
    """Whether the entries `got` are those of the array `out` of memo."""
    want = numpy.broadcast_to(numpy.asarray(out), sizes).ravel()
    # memo adds in single precision, and a model with many choices adds many numbers
    return len(got) == len(want) and all(
        abs(g - w) < 1e-4 * max(1, abs(w)) for g, w in zip(got, want))


def main() -> int:
    examples = importlib.import_module(
        next((a for a in sys.argv[1:] if not a.startswith('-')), 'examples'))
    raw = list(examples.MODELS)
    args_of = getattr(examples, "ARGS", {})
    text, sizes = source(raw, vars(examples), args_of)
    try:
        results, reasons = run(text)
    except RuntimeError as e:
        print(e)
        return 1

    scope = vars(examples)
    scope["memo"] = memo
    failed = 0
    for f, got, reason in zip(raw, results, reasons, strict=True):
        # memo compiles a model in the scope of its caller, which has to be the module of the model
        try:
            exec(f"{f.__name__} = memo({f.__name__})", scope)
            out = scope[f.__name__](*args_of.get(f.__name__, ()))
        except MemoError:
            out = None
        if got is None or out is None:
            ok = got is None and out is None
            failed += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {f.__name__}  (rejected: {reason or 'by memo only'})")
            continue
        ok = agree(got, out, sizes[f.__name__])
        failed += not ok
        print(f"{'ok  ' if ok else 'FAIL'} {f.__name__}")
        if not ok and "-v" in sys.argv:
            want = numpy.broadcast_to(numpy.asarray(out), sizes[f.__name__]).ravel()
            print("   memo:", [round(float(w), 5) for w in want])
            print("   lean:", [round(g, 5) for g in got])
    print(f"{len(raw) - failed} of {len(raw)} models agree")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
