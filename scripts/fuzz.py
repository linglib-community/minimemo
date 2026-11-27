"""Write random memo models to scripts/fuzz_models.py.

    python scripts/fuzz.py [seed] [count]
    python scripts/difftest.py fuzz_models -v
"""
import pathlib
import random
import sys

HEADER = '''from enum import IntEnum

import jax


class U(IntEnum):
    GREEN = 0b0001
    PINK = 0b0010
    SQUARE = 0b0100
    ROUND = 0b1000


class R(IntEnum):
    GREEN_SQUARE = U.GREEN | U.SQUARE
    GREEN_CIRCLE = U.GREEN | U.ROUND
    PINK_CIRCLE = U.PINK | U.ROUND


@jax.jit
def denotes(u, r):
    return (u & r) != 0

'''
VALUES = {"U": [1, 2, 4, 8], "R": [5, 9, 10]}
AGENTS = ["alice", "bob", "carol"]
EARLIER = []  # the models so far that memo accepts and that refer to no other model


class Frame:
    """What an agent can refer to: its own choices, and other agents' choices."""

    def __init__(self):
        self.own = {}        # name -> domain, known to the agent
        self.others = {}     # (agent, name) -> [domain, known]
        self.models = {}     # agent -> Frame
        self.positive = set()  # (agent, name) of others' choices whose weight is never zero

    def copy(self):
        f = Frame()
        f.own, f.positive = dict(self.own), set(self.positive)
        f.others = {k: list(v) for k, v in self.others.items()}
        f.models = {a: m.copy() for a, m in self.models.items()}
        return f


def weight(rng, frame, new, dom, fresh=None, exact=False):
    """A weight for choosing `new` in `dom`, written in the scope of `frame`.

    With `exact`, the weight is a whole number, so that its greatest values are the same in
    floating point. With `fresh`, a supply of names, the weight may imagine a choice.
    """
    opts = ["1", f"1 + {rng.randint(1, 3)} * ({new} == {rng.choice(VALUES[dom])})"]
    for (b, y), (d, known) in frame.others.items():
        if d == dom and known:
            opts.append(f"1 + {rng.randint(1, 2)} * ({new} == {b}.{y})")
    for k, d in frame.own.items():
        if {d, dom} == {"U", "R"} and EARLIER and not exact:
            u, r = (new, k) if dom == "U" else (k, new)
            opts.append(f"1 + {rng.choice(EARLIER)}[{u}, {r}]()")
    if exact:
        for k, d in frame.own.items():
            if {d, dom} == {"U", "R"}:
                u, r = (new, k) if dom == "U" else (k, new)
                opts.append(f"denotes({u}, {r}) + 2 * ({new} == {rng.choice(VALUES[dom])})")
        return rng.choice(opts)
    if fresh is not None:
        for b in AGENTS:
            z, d = next(fresh), rng.choice("UR")
            inner = weight(rng, frame.models.get(b, Frame()), z, d)
            value = new if d == dom and rng.random() < 0.5 else rng.choice(VALUES[d])
            opts.append(f"1 + imagine[{b}: chooses({z} in {d}, wpp={inner}), Pr[{b}.{z} == {value}]]")
    for k, d in frame.own.items():
        if d == dom:
            opts.append(f"1 + {rng.randint(1, 2)} * ({new} == {k})")
        if {d, dom} == {"U", "R"}:
            u, r = (new, k) if dom == "U" else (k, new)
            opts += [f"denotes({u}, {r})", f"1 + 2 * denotes({u}, {r})"]
    for (b, y), (d, known) in frame.others.items():
        if d == dom and not known:
            opts += [f"Pr[{b}.{y} == {new}]", f"1 + Pr[{b}.{y} == {new}] ** 2"]
        if not known:
            opts.append(f"1 + ({new} == {VALUES[dom][0]}) * Pr[{b}.{y} == {rng.choice(VALUES[d])}]")
    return rng.choice(opts)


def model(rng, index):
    root = Frame()                     # the observer: axes are its own, agents' choices are others
    root.own = {"u": "U", "r": "R"}
    lines, fresh = [], iter(f"x{i}" for i in range(99))
    for _ in range(rng.randint(3, 6)):
        a = rng.choice(AGENTS)
        fa = root.models.setdefault(a, Frame())
        kind = rng.choice(["chooses", "chooses", "knows", "thinks", "thinks", "observes",
                           "observes", "event", "forgets", "maximizes", "that", "that", "that",
                           "snapshots", "joint"])
        if kind == "chooses":
            x, d = next(fresh), rng.choice("UR")
            lines.append(f"{a}: chooses({x} in {d}, wpp={weight(rng, fa, x, d, fresh)})")
            fa.own[x] = d
            root.others[(a, x)] = [d, False]
        elif kind == "joint":
            (x, d), (y, e) = (next(fresh), rng.choice("UR")), (next(fresh), rng.choice("UR"))
            with_x = fa.copy()
            with_x.own[x] = d
            w = f"({weight(rng, fa, x, d)}) * ({weight(rng, with_x, y, e)})"
            lines.append(f"{a}: chooses({x} in {d}, {y} in {e}, wpp={w})")
            for z, dz in ((x, d), (y, e)):
                fa.own[z] = dz
                root.others[(a, z)] = [dz, False]
        elif kind == "maximizes":
            x, d = next(fresh), rng.choice("UR")
            lines.append(f"{a}: chooses({x} in {d}, to_maximize={weight(rng, fa, x, d, exact=True)})")
            fa.own[x] = d
            root.others[(a, x)] = [d, False]
        elif kind == "that":
            # an event that the agent gives a positive probability, at most once for each choice
            targets = [k for k, v in fa.others.items() if not v[1] and k in fa.positive]
            if targets:
                b, y = rng.choice(targets)
                test = rng.choice(["==", "!="])
                lines.append(f"{a}: observes_that[{b}.{y} {test} "
                             f"{rng.choice(VALUES[fa.others[(b, y)][0]])}]")
                fa.positive.discard((b, y))
        elif kind == "snapshots":
            past = f"past_{a}"
            if past not in fa.models:
                lines.append(f"{a}: snapshots_self_as({past})")
                fa.models[past] = fa.copy()
                for x, d in fa.own.items():
                    fa.others[(past, x)] = [d, True]
        elif kind == "knows":
            axis = rng.choice("ur")
            if axis not in fa.own:
                lines.append(f"{a}: knows({axis})")
                fa.own[axis] = axis.upper()
                root.others[(a, axis)] = [axis.upper(), True]
        elif kind == "thinks":
            b = rng.choice([c for c in AGENTS if c != a])
            fb = fa.models.setdefault(b, Frame())
            inner = []
            for _ in range(rng.randint(1, 2)):
                y, d = next(fresh), rng.choice("UR")
                w = weight(rng, fb, y, d)
                inner.append(f"{b}: chooses({y} in {d}, wpp={w})")
                fb.own[y] = d
                fa.others[(b, y)] = [d, False]
                if w.startswith("1"):
                    fa.positive.add((b, y))
            lines.append(f"{a}: thinks[{', '.join(inner)}]")
        elif kind == "observes":
            targets = [(k, v) for k, v in fa.others.items() if not v[1]]
            if targets:
                (b, y), v = rng.choice(targets)
                sources = [k for k, d in root.own.items() if d == v[0]]
                sources += [f"{c}.{z}" for (c, z), w in root.others.items() if w[0] == v[0]]
                lines.append(f"{a}: observes [{b}.{y}] is {rng.choice(sources)}")
                v[1] = True
        elif kind == "event":
            targets = [(k, v) for k, v in fa.others.items() if not v[1]]
            if targets:
                (b, y), v = rng.choice(targets)
                lines.append(f"{a}: observes_event(wpp=1 + {rng.randint(1, 3)} * "
                             f"({b}.{y} == {rng.choice(VALUES[v[0]])}))")
        elif kind == "forgets":
            mine = [x for x in fa.own if x not in "ur"]
            if mine and rng.random() < 0.5:
                x = rng.choice(mine)
                lines.append(f"{a}: forgets_about({x})")
                del fa.own[x], root.others[(a, x)]
    terms = ["0 * u + 0 * r"]
    for (a, x), (d, known) in root.others.items():
        axis = d.lower()
        terms.append(f"{rng.randint(1, 3)} * ({a}.{x} == {axis})")
    for a, fa in root.models.items():
        for (b, y), (d, known) in fa.others.items():
            if not known:
                terms.append(f"{a}[Pr[{b}.{y} == {rng.choice(VALUES[d])}]]")
        for past, fp in fa.models.items():
            if past.startswith("past_"):
                for (b, y), (d, known) in fp.others.items():
                    if not known:
                        terms.append(f"{a}[{past}[Pr[{b}.{y} == {rng.choice(VALUES[d])}]]]")
    terms = rng.sample(terms, min(len(terms), 3))
    broken = rng.random() < 0.2 and spoil(rng, root, lines, terms, fresh)
    body = "\n".join("    " + line for line in lines)
    text = f"def fuzz{index}[u: U, r: R]():\n{body}\n    return E[{' + '.join(terms)}]\n"
    if not broken and "fuzz" not in body:
        EARLIER.append(f"fuzz{index}")
    return text


def spoil(rng, root, lines, terms, fresh):
    """Add one statement or term that memo does not accept, if the model has room for one."""
    ways = []
    for a, fa in root.models.items():
        mine = [x for x in fa.own if x not in "ur"]
        unknown = [(k, v[0]) for k, v in fa.others.items() if not v[1]]
        known = [(k, v[0]) for k, v in fa.others.items() if v[1]]
        z = next(fresh)
        for x in mine:  # a choice made twice
            ways.append(("line", f"{a}: chooses({x} in {fa.own[x]}, wpp=1)"))
        for (b, y), d in unknown:
            # a weight that the agent is uncertain of
            ways.append(("line", f"{a}: chooses({z} in {d}, wpp=1 + ({b}.{y} == {z}))"))
            # an observation from the other domain
            ways.append(("line", f"{a}: observes [{b}.{y}] is {'r' if d == 'U' else 'u'}"))
            # a query for a value that the agent is uncertain of
            ways.append(("term", f"{a}[{b}.{y}]"))
            # an imagined value that the agent is uncertain of
            ways.append(("line", f"{a}: chooses({z} in {d}, wpp=imagine["
                                 f"{b}: chooses({z}b in {d}, wpp=1), {b}.{z}b == {z}])"))
        for (b, y), d in known:  # an observation of a choice that the agent is certain of
            ways.append(("line", f"{a}: observes [{b}.{y}] is {d.lower()}"))
        for axis in "ur":  # forgetting a choice that the agent was told
            if axis in fa.own:
                ways.append(("line", f"{a}: forgets_about({axis})"))
        for axis in "ur":  # forgetting a choice that the agent does not have
            if axis not in fa.own:
                ways.append(("line", f"{a}: forgets_about({axis})"))
        if (a, "r") not in root.others:  # a choice that does not exist
            ways.append(("term", f"({a}.r == r)"))
    if not ways:
        return False
    kind, text = rng.choice(ways)
    (lines if kind == "line" else terms).append(text)
    return True


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    rng = random.Random(seed)
    EARLIER.clear()
    models = [model(rng, i) for i in range(count)]
    names = ", ".join(f"fuzz{i}" for i in range(count))
    out = pathlib.Path(__file__).with_name("fuzz_models.py")
    out.write_text(HEADER + "\n\n".join(models) + f"\n\nMODELS = [{names}]\n")


if __name__ == "__main__":
    main()
