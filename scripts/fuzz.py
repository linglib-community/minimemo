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


class Frame:
    """What an agent can refer to: its own choices, and other agents' choices."""

    def __init__(self):
        self.own = {}        # name -> domain, known to the agent
        self.others = {}     # (agent, name) -> [domain, known]
        self.models = {}     # agent -> Frame


def weight(rng, frame, new, dom):
    """A weight for choosing `new` in `dom`, written in the scope of `frame`."""
    opts = ["1", f"1 + {rng.randint(1, 3)} * ({new} == {rng.choice(VALUES[dom])})"]
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
                           "observes", "event", "forgets"])
        if kind == "chooses":
            x, d = next(fresh), rng.choice("UR")
            lines.append(f"{a}: chooses({x} in {d}, wpp={weight(rng, fa, x, d)})")
            fa.own[x] = d
            root.others[(a, x)] = [d, False]
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
                inner.append(f"{b}: chooses({y} in {d}, wpp={weight(rng, fb, y, d)})")
                fb.own[y] = d
                fa.others[(b, y)] = [d, False]
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
            terms.append(f"{a}[Pr[{b}.{y} == {rng.choice(VALUES[d])}]]")
    body = "\n".join("    " + line for line in lines)
    return (f"def fuzz{index}[u: U, r: R]():\n{body}\n"
            f"    return E[{' + '.join(rng.sample(terms, min(len(terms), 3)))}]\n")


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    rng = random.Random(seed)
    models = [model(rng, i) for i in range(count)]
    names = ", ".join(f"fuzz{i}" for i in range(count))
    out = pathlib.Path(__file__).with_name("fuzz_models.py")
    out.write_text(HEADER + "\n\n".join(models) + f"\n\nMODELS = [{names}]\n")


if __name__ == "__main__":
    main()
