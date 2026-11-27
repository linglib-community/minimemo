"""Print a memo model as a minimemo term.

The model is read with memo's own parser, so this file only prints. It covers the grammar of the
memo paper and `knows`: `chooses`, `observes [..] is ..`, `thinks`, `knows`, choices, queries,
`E[..]`, `Pr[..]`, `imagine`, arithmetic, and calls of foreign functions and of other models.

The Lean file that receives the output supplies the types `Agent`, `Name` and `Dom`, the function
`dom`, a Lean function for each foreign function under the same name, and for each referenced
model `m` a function `mRef`. A Python name such as `u_said` becomes `uSaid`. `difftest.py` writes
such a file.

Usage, with memo installed:

    from memo2lean import model
    print(model(f))        # f is the model's function, without the @memo decorator
"""
from fractions import Fraction
from textwrap import indent

from memo.core import (EChoice, EExpect, EFFI, EImagine, ELit, EMemo, EOp, EWith, Op, SChoose,
                       SForAll, SKnows, SShow, SWith)
from memo.parse import parse_memo

BINARY = {Op.ADD: "(· + ·)", Op.SUB: "(· - ·)", Op.MUL: "(· * ·)", Op.DIV: "(· / ·)", Op.EQ: "eq"}


class Unsupported(Exception):
    """The model uses a construct outside the grammar of the memo paper."""


KEYWORDS = {"at", "by", "do", "else", "end", "from", "fun", "have", "if", "in", "let", "open",
            "show", "then", "with"}


def ident(name: str) -> str:
    head, *rest = name.split("_")
    out = head + "".join(word[:1].upper() + word[1:] for word in rest)
    return f"«{out}»" if out in KEYWORDS else out


def lit(value) -> str:
    q = Fraction(value)
    return f".lit {q.numerator}" if q.denominator == 1 and q >= 0 else f".lit ({q})"


def choice(who: str, name: str) -> str:
    here = f".choice .{ident(name)}"
    return here if who == "self" else f".query .{ident(who)} ({here})"


def call(name: str, args: list[str]) -> str:
    if len(args) in (1, 2):
        return f".op{'₁₂'[len(args) - 1]} {ident(name)} " + " ".join(f"({a})" for a in args)
    applied = " ".join(f"(v {i})" for i in range(len(args)))
    return f".op (fun v ↦ {ident(name)} {applied}) ![{', '.join(args)}]"


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
        case EOp(op=op, args=[a, b]) if op in BINARY:
            return f".op₂ {BINARY[op]} ({expr(a)}) ({expr(b)})"
        case EFFI(name=name, args=args, kwargs=kwargs) if not kwargs:
            return call(name, [expr(a) for a in args])
        case EMemo(name=name, args=[], ids=ids, kwargs=kwargs) if not kwargs:
            return call(name + "_ref", [choice(who, c) for (_, who, c) in ids])
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
    return " ;;\n".join(out)


def model(f, name: str | None = None) -> str:
    _, ss, rets = parse_memo(f)
    if len(rets) != 1:
        raise Unsupported("a model with several return values")
    axes = ", ".join(f"(.{ident(s.id)}, .{s.domain})" for s in ss if isinstance(s, SForAll))
    body = stmts([s for s in ss if not isinstance(s, SForAll)])
    return (f"def {ident(name or f.__name__)} : Model Agent Name Dom ℚ where\n"
            f"  axes := [{axes}]\n  body :=\n{indent(body, '    ')}\n  ret := {expr(rets[0])}\n")
