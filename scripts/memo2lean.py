"""Print a memo model as a Lean term.

Uses memo's own parser, so memo must be installed.

    from memo2lean import model
    print(model(f))    # f is the model function, without @memo
"""
from fractions import Fraction
from textwrap import indent

from memo.core import (EChoice, EExpect, EFFI, EImagine, EInline, ELit, EMemo, EOp, EWith, Op, SChoose,
                       SForAll, SForgetsAbout, SKnows, SObserves, SShow, SSnapshot, SWith)
from memo.parse import parse_memo

# The operators of memo that minimemo has, by the name of the constructor of `Memo.Prim`.
BINARY = {Op.ADD: "add", Op.SUB: "sub", Op.MUL: "mul", Op.DIV: "div", Op.EQ: "eq", Op.NEQ: "ne",
          Op.LT: "lt", Op.LTE: "le", Op.AND: "both", Op.OR: "either"}
SWAPPED = {Op.GT: "lt", Op.GTE: "le"}  # a > b is b < a
UNARY = {Op.NEG: "neg", Op.ABS: "abs"}
# Operators that are not rational: they are outside functions, with a meaning over the reals.
OUTSIDE = {Op.EXP: "exp", Op.LOG: "log", Op.POW: "rpow"}


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
        case EFFI(name=name):
            return name in BOOLEAN_FUNCTIONS
        case ELit(value=bool()):
            return True
    return False


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
            return f".query .{ident(who)} ({expr(inner)})"
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
        case EFFI(name=name, args=args, kwargs=kwargs) if not kwargs:
            return call(ident(name), [expr(a) for a in args])
        case EMemo(name=name, args=args, ids=ids, kwargs=kwargs) if not kwargs:
            head = ident(name) + "".join(f" {static(a)}" for a in args)
            return f".ref (.{head}) ![{', '.join(choice(who, c) for (_, who, c) in ids)}]"
        case EImagine(do=do, then=then):
            return f".imagine ({stmts(do)}) ({expr(then)})"
    raise Unsupported(type(e).__name__)


def ref(who: str) -> str:
    return ".self" if who == "self" else f"(.agent .{ident(who)})"


def stmt(s) -> str:
    match s:
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
            return f".snapshot .{ident(who)} .{ident(alias)}"
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
            inner = " ;;\n".join(stmt(s.stmt) for s in ss[i:j])
            out.append(f".thinks .{ident(ss[i].who)}\n" + indent(f"({inner})", "  "))
            i = j
        else:
            out.append(stmt(ss[i]))
            i += 1
    return " ;;\n".join(out) if out else ".pass"


def model(f, name: str | None = None) -> str:
    pctxt, ss, rets = parse_memo(f)
    params = " ".join(map(ident, pctxt.static_parameters))
    binder = f" ({params} : ℚ)" if params else ""
    if len(rets) != 1:
        raise Unsupported("a model with several return values")
    axes = ", ".join(f"(.{ident(s.id)}, .{s.domain})" for s in ss if isinstance(s, SForAll))
    body = stmts([s for s in ss if not isinstance(s, SForAll)])
    return (f"def {ident(name or f.__name__)}{binder} : Model Agent Name Dom (Refs Ix Fn) where\n"
            f"  axes := [{axes}]\n  body :=\n{indent(body, '    ')}\n  ret := {expr(rets[0])}\n")
