"""Run memo models in Lean, and compare the arrays with those of memo."""
import dataclasses
import itertools
import operator
import os
import pathlib
import re
import signal
import subprocess
import sys
from fractions import Fraction

import jax
import numpy
from memo import memo
from memo.lib import Bool
from memo.core import MemoError
from memo.core import (EChoice, EFFI, EInline, ELit, EMemo, EOp, EWith, Op, SChoose, SForAll, SKnows, SShow, SSnapshot,
                       SWith)
from memo.parse import parse_memo

import enum

import memo2lean
from memo2lean import Rejected, Unsupported, ident, model

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEPTH = 64  # how deep references between models are followed


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


ARITHMETIC = {Op.ADD: operator.add, Op.SUB: operator.sub, Op.MUL: operator.mul,
              Op.DIV: operator.truediv, Op.NEG: operator.neg, Op.UADD: operator.pos}


def native(v):
    """A value as memo's own functions take it: a whole number as an integer."""
    return int(v) if float(v) == int(v) else float(v)


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
    outside = sorted({memo2lean.outside_of(n) for _, ss, rets in parsed.values()
                      for n in nodes([ss, rets])} - {None})
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
    domains = sorted({d for ds in domain_of.values() for d in ds})
    env = {"Bool": Bool} | dict(env)  # memo's own domain of the two truth values
    memo2lean.INLINE_ENV = env
    values = {d: [number(v) for v in env[d]] for d in domains}
    # a table has an entry for each joint value of its choices, so large domains are not run
    if any(len(vs) > 64 for vs in values.values()):
        raise Unsupported("a domain with more than 64 values")
    exact = (lambda v: v) if outside else (lambda v: Fraction(float(v)))

    def possible(e) -> set:
        """The values that an argument of an outside function can take."""
        match e:
            case EChoice(id=x):
                return {exact(v) for d in domain_of[x] for v in values[d]}
            case EWith(expr=inner):
                return possible(inner)
            case ELit(value=v) if not isinstance(v, str):
                return {exact(v)}
            case EInline(val=v):
                return {exact(number(eval(v, dict(env))))}
            case EOp(op=op, args=args) if op in ARITHMETIC:
                combos = itertools.product(*map(possible, args))
                return {ARITHMETIC[op](*c) for c in itertools.islice(combos, 4097)}
        raise Unsupported("a function applied to something other than arithmetic on choices")

    memo2lean.EXOTIC = {name: set(p[0].exotic_parameters) for name, p in parsed.items()}
    memo2lean.BOUND_IDS.clear()
    # the arrays that the parameters of the models shown hold, by the name of the parameter
    arrays = {}
    for f in shown:
        ctxt, given_here = parsed[f.__name__][0], list(args_of.get(f.__name__, ()))
        for i, param in enumerate(ctxt.static_parameters):
            if i < len(given_here):
                value = given_here[i]
            elif ctxt.static_defaults[i] is not None:
                value = eval(ctxt.static_defaults[i], dict(env))
            else:
                raise Unsupported("a model that is given no parameters")
            if param in ctxt.exotic_parameters:
                if not isinstance(value, jax.numpy.ndarray):
                    raise Rejected(f"the parameter {param} is not an array")
                arrays[param] = value
            elif numpy.ndim(value) > 0:
                raise Rejected(f"the parameter {param} is not a number")

    def fixed(what):
        return arrays[what] if what in arrays else eval(what, dict(env))

    functions = {}  # each outside function, taking the arguments given by keyword last
    for model_name, (ctxt, ss, rets) in parsed.items():
        memo2lean.EXOTIC_HERE.clear(); memo2lean.EXOTIC_HERE.update(ctxt.exotic_parameters)
        for n in nodes([ss, rets]):
            if isinstance(n, EFFI):
                name, args = memo2lean.effective(n)
                keys, base, k = list(n.kwargs), env[n.name], len(n.args)
                held = {i: fixed(what) for i, what in memo2lean.bindings(n).items()}

                def function(*p, base=base, keys=keys, k=k, held=held):
                    p, full = list(p), []
                    for i in range(len(p) + len(held)):
                        full.append(held[i] if i in held else p.pop(0))
                    return base(*full[:k], **dict(zip(keys, full[k:])))
                functions[name] = function
                slots = calls.setdefault(name, [set() for _ in args])
                for slot, arg in zip(slots, args):
                    slot |= possible(arg)
    for name, slots in calls.items():
        point = [native(min(slot)) for slot in slots]
        if numpy.asarray(functions[name](*point)).dtype == bool:
            memo2lean.BOOLEAN_FUNCTIONS.add(name)
    memo2lean.SIGNATURES = {name: (list(p[0].static_parameters), list(p[0].static_defaults))
                            for name, p in parsed.items()}
    memo2lean.RETURNS = {name: len(p[2]) for name, p in parsed.items()}
    each = memo2lean.def_names

    # the models, translated: the translation of `wants` adds agents and names of its own
    memo2lean.EXTRA_AGENTS.clear(); memo2lean.EXTRA_NAMES.clear()
    texts = [model(f) for f in raw]
    agents += memo2lean.EXTRA_AGENTS
    names += memo2lean.EXTRA_NAMES

    def axes_of(name):
        return [s.domain for s in parsed[name][1] if isinstance(s, SForAll)]

    def applied(name, ps):
        return f"{ident(name)} {' '.join(ps)}" if ps else ident(name)

    def params(name):
        return [ident(p) for p in parsed[name][0].static_parameters
                if p not in parsed[name][0].exotic_parameters]

    # the outside functions of the models, and an index for each model with its parameters
    fns = [f"  | {ident(name)} : Fn {len(slots)}" for name, slots in calls.items()]
    fns += [f"  | {name} : Fn {memo2lean.OUTSIDE_ARITY[name]}" for name in outside]
    indices = [f"  | {ident(n)}{''.join(f' ({p} : ℚ)' for p in params(name))}"
               for name in parsed for n in each(name)]
    lean = ["import Minimemo", "import Mathlib.Algebra.Order.Field.Rat", "",
            "open Memo", "open scoped Memo", "",
            "namespace Translated  -- a model may have the name of something in Lean", "",
            f"inductive Agent{bars(map(ident, agents))} deriving DecidableEq, Repr",
            f"inductive Name{bars(map(ident, names))} deriving DecidableEq, Repr",
            f"inductive Dom{bars(domains)} deriving DecidableEq",
            "inductive Fn : ℕ → Type", *fns,
            "inductive Ix", *indices, "  deriving DecidableEq", "",
            f"def dom : Dom → Domain {K}" + ("" if domains else " := fun d ↦ nomatch d")]
    for d in domains:
        vs = ", ".join(num(v) for v in values[d])
        lean.append(f"  | .{d} => ⟨{len(values[d])}, fun j ↦ ([{vs}] : List {K}).getD j 0⟩")
    lean.append("")
    for name, slots in calls.items():
        f = functions[name]
        columns = [sorted(slot) for slot in slots]
        if numpy.prod([len(c) for c in columns]) > 4096:
            raise Unsupported("a function with too many values to list")
        points = itertools.product(*columns)
        def value(p):
            out = f(*map(native, p))
            if numpy.ndim(out) > 0:
                raise Rejected("an outside function that does not return a number")
            return num(number(out))
        rows = ", ".join(f"([{', '.join(num(v) for v in p)}], {value(p)})" for p in points)
        args = " ".join(f"a{i}" for i in range(len(slots)))
        binder = f" ({args} : {K})" if slots else ""
        lean += [f"def {ident(name)}{binder} : {K} :=",
                 f"  (List.lookup [{', '.join(args.split())}] "
                 f"([{rows}] : List (List {K} × {K}))).getD 0", ""]
    lean += texts
    of = ".ofFloat" if outside else ".ofField"
    if calls or outside:
        lean.append(f"def call : {{k : ℕ}} → Fn k → (Fin k → {K}) → {K}")
        lean += [f"  | _, .{name} => Exp.float .{name}" for name in outside]
        for name, slots in calls.items():
            args = " ".join(f"(v {i})" for i in range(len(slots)))
            lean.append(f"  | _, .{ident(name)} => fun v ↦ {ident(name)} {args}")
    else:
        lean.append(f"def call : {{k : ℕ}} → Fn k → (Fin k → {K}) → {K} := fun f _ ↦ nomatch f")
    # the models are a family in which a reference names a model with its parameters, as in memo
    lean += ["", "def fam : Family Agent Name Dom Fn Ix Ix where", "  model"]
    lean += [f"    | .{applied(n, params(name))} => {applied(n, params(name))}"
             for name in parsed for n in each(name)]
    lean += ["  target _ r := r", "",
             f"def interp (p : Ix) : Interp Dom (Refs Ix Fn) {K} :=",
             f"  {of} dom (fam.call dom call (fam.entries {of} dom call {DEPTH}) p)", ""]
    # an array is printed as text: Lean's own display of a long list of numbers can fail
    lean += [f"def render : Option (List {K}) → String",
             '  | some l => "some [" ++ ", ".intercalate (l.map toString) ++ "]"',
             '  | none => "none"', ""]
    given = {f.__name__: [rat(a) for a, p in zip(args_of.get(f.__name__, ()),
                                                 parsed[f.__name__][0].static_parameters)
                          if p not in parsed[f.__name__][0].exotic_parameters] for f in shown}
    shown_names = [(f.__name__, n) for f in shown for n in each(f.__name__)]
    for name, n in shown_names:
        m = applied(n, given[name])
        lean.append(f"#eval IO.println (render (Model.entries (interp (.{m})) ({m})))")
    lean.append('#eval "errors"')
    for name, n in shown_names:  # why each model is not accepted, if it is not
        lean.append(f"#eval Model.error ({applied(n, given[name])})")
    sizes = {f.__name__: [len(values[d]) for d in axes_of(f.__name__)] for f in shown}
    lean.append("end Translated")
    return "\n".join(lean) + "\n", sizes


def run(text, path, timeout=None):
    """The arrays and the reasons for rejection that Lean prints for the file `text`: for each
    model shown, the entries of its array or `None`, and the reason or `None`."""
    path.parent.mkdir(exist_ok=True, parents=True)
    path.write_text(text)
    # Lean runs in a process group of its own, so that when time runs out all of it is stopped:
    # stopping `lake` alone leaves the `lean` that it started running
    proc = subprocess.Popen(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.communicate()
        raise
    if proc.returncode != 0:
        raise RuntimeError(out + err)
    arrays, _, errors = out.partition('"errors"')
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


def verdict(name, results, reasons, out, sizes) -> tuple[bool, str]:
    """Whether minimemo gives what memo gives for a model: the next results are its arrays, one for
    each value that it returns, and `out` is what memo returns, or `None` if memo rejects it."""
    count = memo2lean.RETURNS.get(name, 1)
    gots = [next(results) for _ in range(count)]
    why = [next(reasons) for _ in range(count)][0]
    if out is None or None in gots:
        rejected = "minimemo rejects it" if None in gots else "memo rejects it"
        return out is None and all(g is None for g in gots), f"only {rejected}: {why}"
    outs = list(out) if count > 1 else [out]
    for got, o in zip(gots, outs, strict=True):
        if not agree(got, o, sizes[name]):
            want = numpy.broadcast_to(numpy.asarray(o), sizes[name]).ravel()
            return False, (f"memo: {[round(float(w), 5) for w in want]}\n"
                           f"lean: {[round(g, 5) for g in got]}")
    return True, ""


def compare(module) -> dict:
    """For each model of a module, whether memo and minimemo give the same array or both reject
    the model, with what differs if they do not."""
    raw = list(module.MODELS)
    args_of = getattr(module, "ARGS", {})
    text, sizes = source(raw, vars(module), args_of)
    results, reasons = run(text, ROOT / "scratch" / f"{module.__name__}.lean")
    scope = vars(module)
    scope["memo"] = memo
    verdicts = {}
    results, reasons = iter(results), iter(reasons)
    for f in raw:
        # memo compiles a model in the scope of its caller, which has to be the module of the model
        try:
            exec(f"{f.__name__} = memo({f.__name__})", scope)
            out = scope[f.__name__](*args_of.get(f.__name__, ()))
        except MemoError:
            out = None
        verdicts[f.__name__] = verdict(f.__name__, results, reasons, out, sizes)
    return verdicts
