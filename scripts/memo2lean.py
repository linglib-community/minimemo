"""Print a memo model as a Lean term.

Uses memo's own parser, so memo must be installed.

    from memo2lean import model
    print(model(f))    # f is the model function, without @memo
"""
from fractions import Fraction
from textwrap import indent

import contextlib
import dataclasses

from memo.core import (EChoice, EEntropy, EExpect, EFFI, EImagine, EInline, EKL, ELit, EMemo, EOp,
                       EPredict, EUtil,
                       EWith, Op, SChoose, SForAll, SForgetsAbout, SGuess, SKnows, SObserves,
                       SPass, SShow, SSnapshot, SWants, SWith)
from memo.parse import parse_memo

# The operators of memo that minimemo has, by the name of the constructor of `Memo.Prim`.
BINARY = {Op.ADD: "add", Op.SUB: "sub", Op.MUL: "mul", Op.DIV: "div", Op.EQ: "eq", Op.NEQ: "ne",
          Op.LT: "lt", Op.LTE: "le", Op.AND: "both", Op.OR: "either"}
SWAPPED = {Op.GT: "lt", Op.GTE: "le"}  # a > b is b < a
UNARY = {Op.NEG: "neg", Op.ABS: "abs"}
# Operators that are not rational: they are outside functions, with a meaning over the reals.
OUTSIDE = {Op.EXP: "exp", Op.LOG: "log", Op.POW: "rpow"}
# Their numbers of arguments, with those of the terms of an entropy and of a divergence.
OUTSIDE_ARITY = {"exp": 1, "log": 1, "rpow": 2, "negMulLog": 1, "klTerm": 2}


def outside_of(n) -> str | None:
    """The operator outside the rational numbers that a syntax node uses, if it uses one."""
    match n:
        case EOp(op=op) if op in OUTSIDE:
            return OUTSIDE[op]
        case EEntropy():
            return "negMulLog"
        case EKL():
            return "klTerm"
    return None


# Where the translation is: the agents from the model, or from an `imagine`, down to the agent
# whose mind an expression is read in, and the statements that follow the current one. memo's
# `Predict` and `wants` are defined from these.
PREFIX: list[str] = []
CONTINUATION: list = []
# The goals that each agent wants, by name; the domain of each choice; the agents and the names
# of choices that the translation adds.
GOALS: dict[str, dict] = {}
DOMAIN: dict[str, str] = {}
SIGNATURES: dict[str, tuple[list, list]] = {}  # the parameters and defaults of each model
RETURNS: dict[str, int] = {}  # how many values each model returns


def def_names(name: str, count: int | None = None) -> list[str]:
    """The names of the Lean models of a memo model: one for each value that it returns."""
    count = RETURNS.get(name, 1) if count is None else count
    return [name] if count == 1 else [f"{name}_r{k}" for k in range(count)]
EXTRA_AGENTS: list[str] = []
EXTRA_NAMES: list[str] = []


@contextlib.contextmanager
def frame(who: str):
    """Translate inside the mind of the agent `who`."""
    PREFIX.append(who)
    try:
        yield
    finally:
        PREFIX.pop()


def fresh(base: str, used: list[str]) -> str:
    name = f"{base}_{len(used) + 1}"
    used.append(name)
    return name


def predict(e) -> str:
    """memo's `Predict[e]`: the agent imagines a copy of itself that makes the statements that
    follow, and expects `e` of the copy. The construction is memo's own, in `core.py`."""
    if not PREFIX:
        raise Unsupported("a prediction by the model itself")
    me = PREFIX[-1]
    future = fresh(f"future_{me}", EXTRA_AGENTS)
    GOALS[future] = dict(GOALS.get(me, {}))
    todo = []
    for s in CONTINUATION:
        for who in PREFIX[:-1]:
            if isinstance(s, SWith) and s.who == who:
                s = s.stmt
            else:
                break
        else:
            if isinstance(s, SForAll):
                raise Unsupported("an axis after a prediction")
            if isinstance(s, SPass):
                todo.append(s)
            elif getattr(s, "who", None) == me:
                if isinstance(s, SKnows):
                    raise Unsupported("a `knows` after a prediction")
                if isinstance(s, SShow):
                    guess = fresh(s.target_id, EXTRA_NAMES)
                    DOMAIN[guess] = DOMAIN[s.target_id]
                    todo.append(SGuess(future, guess, s.target_who, s.target_id, loc=s.loc))
                    s = dataclasses.replace(s, source_who=future, source_id=guess)
                todo.append(dataclasses.replace(s, who=future))
    saved = PREFIX[:], CONTINUATION[:]
    PREFIX.clear()
    try:
        body = stmts(todo)
        CONTINUATION.clear()
        with frame(future):
            then = expr(e)
    finally:
        PREFIX[:], CONTINUATION[:] = saved
    first = f".snapshot .self .{ident(future)}"
    return f".imagine ({first} ;;\n{indent(body, '  ')}) (.expect (.query .{ident(future)} ({then})))"


# The names that a Python expression in braces may use: the module of the model.
INLINE_ENV: dict = {}

# Names of foreign functions that return booleans. memo adds two booleans as "or".
BOOLEAN_FUNCTIONS: set[str] = set()
BOOLEAN_OPS = {Op.EQ, Op.NEQ, Op.LT, Op.LTE, Op.GT, Op.GTE, Op.AND, Op.OR}


def is_boolean(e) -> bool:
    match e:
        case EOp(op=op) if op in BOOLEAN_OPS:
            return True
        case EOp(op=Op.ADD | Op.MUL, args=[a, b]):
            return is_boolean(a) and is_boolean(b)
        case EFFI():
            return effective(e)[0] in BOOLEAN_FUNCTIONS
        case ELit(value=bool()):
            return True
    return False


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


class Unsupported(Exception):
    """The model uses a construct outside the grammar of the memo paper."""


KEYWORDS = {"at", "by", "do", "else", "end", "from", "fun", "have", "if", "in", "let", "open",
            "show", "then", "with"}


def ident(name: str) -> str:
    head, *rest = name.split("_")
    out = head + "".join(word[:1].upper() + word[1:] for word in rest)
    return f"«{out}»" if out in KEYWORDS else out


def lit(value) -> str:
    if isinstance(value, str):
        return f".lit {ident(value)}"
    q = Fraction(value)
    return f".lit {q.numerator}" if q.denominator == 1 and q >= 0 else f".lit ({q})"


def choice(who: str, name: str) -> str:
    here = f".choice .{ident(name)}"
    return here if who == "self" else f".query .{ident(who)} ({here})"


STATIC_BINARY = {Op.ADD: "+", Op.SUB: "-", Op.MUL: "*", Op.DIV: "/"}
STATIC_TEST = {Op.EQ: "=", Op.NEQ: "≠", Op.LT: "<", Op.LTE: "≤", Op.GT: ">", Op.GTE: "≥"}


def is_static(e) -> bool:
    """Whether an expression depends only on the parameters of the model."""
    match e:
        case ELit():
            return True
        case EOp(args=args):
            return all(is_static(a) for a in args)
    return False


def static(e) -> str:
    """A number that depends only on the parameters of the model, as a rational number of Lean."""
    match e:
        case ELit(value=str(name)):
            return ident(name)
        case ELit(value=value):
            q = Fraction(value)
            return str(q.numerator) if q.denominator == 1 and q >= 0 else f"({q})"
        case EOp(op=Op.NEG, args=[a]):
            return f"(-{static(a)})"
        case EOp(op=op, args=[a, b]) if op in STATIC_BINARY:
            return f"({static(a)} {STATIC_BINARY[op]} {static(b)})"
    raise Unsupported("an argument of a model reference that is not arithmetic on parameters")


def static_test(e) -> str:
    """A test that depends only on the parameters of the model, as a proposition of Lean."""
    match e:
        case EOp(op=op, args=[a, b]) if op in STATIC_TEST:
            return f"{static(a)} {STATIC_TEST[op]} {static(b)}"
    raise Unsupported("a test on parameters that is not a comparison")


def effective(e) -> tuple[str, list]:
    """An outside function with its arguments in order. Arguments given by keyword follow the
    others, and their keywords are part of the name: the function is a different one with them."""
    if not e.kwargs:
        return e.name, list(e.args)
    return e.name + "__" + "_".join(e.kwargs), list(e.args) + list(e.kwargs.values())


def reference_args(name: str, args: list, kwargs: dict) -> list[str]:
    """The parameters of a model that is referred to, in the order of the model: those given in
    order, then each of the rest by its keyword or by its default."""
    if name not in SIGNATURES:
        if kwargs:
            raise Unsupported("a reference by keyword to a model that is not a memo model")
        return [static(a) for a in args]
    params, defaults = SIGNATURES[name]
    out = [static(a) for a in args]
    for param, default in list(zip(params, defaults))[len(args):]:
        if param in kwargs:
            out.append(static(kwargs[param]))
        elif default is not None:
            q = Fraction(float(eval(default, dict(INLINE_ENV))))
            out.append(str(q.numerator) if q.denominator == 1 and q >= 0 else f"({q})")
        else:
            raise Unsupported("a reference to a model that leaves a parameter out")
    return out


def prim(name: str, args: list[str]) -> str:
    """An operator of memo applied to expressions."""
    return f".prim {name} ![{', '.join(args)}]"


def call(name: str, args: list[str]) -> str:
    """An outside function applied to expressions."""
    return f".fn (.{name}) ![{', '.join(args)}]"


def expr(e) -> str:
    match e:
        case ELit(value=value):
            return lit(value)
        case EChoice(id=name):
            return f".choice .{ident(name)}"
        case EWith(who=who, expr=inner):
            with frame(who):
                return f".query .{ident(who)} ({expr(inner)})"
        case EEntropy(rvs=rvs):
            xs = ", ".join(f"({ref(who)}, .{ident(x)})" for who, x in rvs)
            return f".entropy (.inr .negMulLog) [{xs}]"
        case EKL(p_who=pw, p_id=px, q_who=qw, q_id=qx):
            return f".divergence (.inr .klTerm) ({ref(pw)}, .{ident(px)}) ({ref(qw)}, .{ident(qx)})"
        case EPredict(expr=inner):
            return predict(inner)
        case EUtil(goal=goal):
            if not PREFIX or goal not in GOALS.get(PREFIX[-1], {}):
                raise Unsupported("a goal that the agent does not have")
            return predict(GOALS[PREFIX[-1]][goal])
        case EExpect(expr=inner, reduction="expectation"):
            return f".expect ({expr(inner)})"
        case EExpect(expr=inner, reduction="variance"):
            x = expr(inner)
            square = "(.pow 2)"
            return prim(".sub", [f".expect ({prim(square, [x])})", prim(square, [f".expect ({x})"])])
        case EOp(op=Op.POW, args=[a, ELit(value=int(n))]) if n >= 0:
            return prim(f"(.pow {n})", [expr(a)])
        case EOp(op=Op.UADD, args=[a]):
            return expr(a)
        case EOp(op=Op.INV, args=[a]):  # memo's `not`: true where the number is zero
            return prim(".eq", [expr(a), ".lit 0"])
        case EOp(op=Op.XOR, args=[a, b]) if is_boolean(a) and is_boolean(b):
            return prim(".ne", [expr(a), expr(b)])
        case EInline(val=val):  # a Python expression in braces: a constant of the model
            return lit(float(eval(val, dict(INLINE_ENV))))
        case EOp(op=op, args=[a]) if op in UNARY:
            return prim("." + UNARY[op], [expr(a)])
        case EOp(op=Op.ITE, args=[c, a, b]) if is_static(c):
            # memo decides a test on parameters when it builds the model, so only one branch exists
            return f"(if {static_test(c)} then {expr(a)} else {expr(b)})"
        case EOp(op=Op.ITE, args=[c, a, b]):
            return prim(".ite", [expr(c), expr(a), expr(b)])
        case EOp(op=Op.ADD, args=[a, b]) if is_boolean(a) and is_boolean(b):
            return prim(".either", [expr(a), expr(b)])
        case EOp(op=op, args=[a, b]) if op in BINARY:
            return prim("." + BINARY[op], [expr(a), expr(b)])
        case EOp(op=op, args=[a, b]) if op in SWAPPED:
            return prim("." + SWAPPED[op], [expr(b), expr(a)])
        case EOp(op=op, args=args) if op in OUTSIDE:
            return call(OUTSIDE[op], [expr(a) for a in args])
        case EFFI():
            name, args = effective(e)
            return call(ident(name), [expr(a) for a in args])
        case EMemo(name=name, args=args, ids=ids, kwargs=kwargs, which_retval=which):
            count = RETURNS.get(name, 1)
            if (which is None) != (count == 1) or (which or 0) >= count:
                raise Unsupported("a reference to a value that the model does not return")
            head = ident(def_names(name)[which or 0]) + "".join(
                f" {a}" for a in reference_args(name, args, kwargs))
            return f".ref (.{head}) ![{', '.join(choice(who, c) for (_, who, c) in ids)}]"
        case EImagine(do=do, then=then):
            saved = PREFIX[:], CONTINUATION[:]
            PREFIX.clear()
            try:
                body = stmts(do)
                if do:
                    CONTINUATION.clear()
                return f".imagine ({body}) ({expr(then)})"
            finally:
                PREFIX[:], CONTINUATION[:] = saved
    raise Unsupported(type(e).__name__)


def ref(who: str) -> str:
    return ".self" if who == "self" else f"(.agent .{ident(who)})"


def stmt(s) -> str:
    who = getattr(s, "who", None)
    if isinstance(s, (SChoose, SObserves, SWith)):
        with frame(who):
            return stmt_in(s)
    return stmt_in(s)


def stmt_in(s) -> str:
    match s:
        case SPass():
            return ".pass"
        case SWants(who=who, what=what, how=how):  # a goal is used where the agent refers to it
            GOALS.setdefault(who, {})[what] = EExpect(how, reduction="expectation", warn=False,
                                                     loc=s.loc, static=False)
            return ".pass"
        case SGuess(who=who, id=name, target_who=b, target_id=x):
            with frame(who):
                same = prim(".eq", [f".choice .{ident(name)}",
                                    f".query .{ident(b)} (.choice .{ident(x)})"])
            return f".chooses .{ident(who)} .{ident(name)} .{DOMAIN[x]}\n  (.expect ({same}))"
        case SChoose(who=who, choices=[(name, domain)], wpp=wpp, reduction="normalize"):
            head = f".chooses .{ident(who)} .{ident(name)} .{domain}"
            weight = f"({expr(wpp)})"
            return f"{head} {weight}" if len(head) + len(weight) < 88 else f"{head}\n  {weight}"
        case SShow(who=who, target_who=b, target_id=x, source_who=g, source_id=y):
            return f".observes .{ident(who)} .{ident(b)} .{ident(x)} {ref(g)} .{ident(y)}"
        case SChoose(who=who, choices=choices, wpp=wpp, reduction="normalize"):
            xs = ", ".join(f"(.{ident(x)}, .{d})" for x, d in choices)
            return f".choosesMany .{ident(who)} [{xs}]\n  ({expr(wpp)})"
        case SChoose(who=who, choices=[(name, domain)], wpp=wpp, reduction="maximize"):
            return f".choosesMax .{ident(who)} .{ident(name)} .{domain}\n  ({expr(wpp)})"
        case SSnapshot(who=who, alias=alias):
            return f".snapshot (.agent .{ident(who)}) .{ident(alias)}"
        case SForgetsAbout(who=who, ids=ids):
            return f".forgets .{ident(who)} [{', '.join('.' + ident(x) for x in ids)}]"
        case SObserves(who=who, what=what, how="probability"):
            return f".observesEvent .{ident(who)} ({expr(what)})"
        case SObserves(who=who, what=what, how="boolean"):
            return f".observesEvent .{ident(who)} ({prim('.truthy', [expr(what)])})"
        case SKnows(who=who, source_who=g, source_id=y):
            return f".knows .{ident(who)} {ref(g)} .{ident(y)}"
        case SWith(who=who, stmt=inner):
            return f".thinks .{ident(who)} ({stmt(inner)})"
    raise Unsupported(type(s).__name__)


def stmts(ss) -> str:
    """Statements in sequence. Consecutive statements that one agent thinks are put together."""
    out, i = [], 0
    while i < len(ss):
        if isinstance(ss[i], SWith):
            j = i
            while j < len(ss) and isinstance(ss[j], SWith) and ss[j].who == ss[i].who:
                j += 1
            inner = []
            for k in range(i, j):
                CONTINUATION[:] = ss[k + 1:]
                with frame(ss[i].who):
                    inner.append(stmt(ss[k].stmt))
            out.append(f".thinks .{ident(ss[i].who)}\n" + indent("(" + " ;;\n".join(inner) + ")", "  "))
            i = j
        else:
            CONTINUATION[:] = ss[i + 1:]
            out.append(stmt(ss[i]))
            i += 1
    return " ;;\n".join(out) if out else ".pass"


def model(f, name: str | None = None) -> str:
    pctxt, ss, rets = parse_memo(f)
    params = " ".join(map(ident, pctxt.static_parameters))
    binder = f" ({params} : ℚ)" if params else ""
    PREFIX.clear(); CONTINUATION.clear(); GOALS.clear()
    for n in nodes([ss, rets]):
        match n:
            case SForAll(id=x, domain=d):
                DOMAIN[x] = d
            case SChoose(choices=cs):
                DOMAIN.update(cs)
    axes = ", ".join(f"(.{ident(s.id)}, .{s.domain})" for s in ss if isinstance(s, SForAll))
    body = stmts([s for s in ss if not isinstance(s, SForAll)])
    PREFIX.clear(); CONTINUATION.clear()
    return "\n".join(
        f"def {ident(n)}{binder} : Model Agent Name Dom (Refs Ix Fn) where\n"
        f"  axes := [{axes}]\n  body :=\n{indent(body, '    ')}\n  ret := {expr(ret)}\n"
        for n, ret in zip(def_names(name or f.__name__, len(rets)), rets))
