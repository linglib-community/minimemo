"""The example models of minimemo as memo source, printed as minimemo terms.

`U`, `R` and `denotes` follow the Rational Speech Acts demonstration in the memo repository,
which its authors distribute under the MIT licence.
Run with memo installed: `python scripts/examples.py`.
"""
from enum import IntEnum

import jax

from memo2lean import model


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


@jax.jit
def count(u):
    return sum(1.0 * denotes(u, int(r)) for r in R)


def naive[u: U, r: R]():
    listener: thinks[
        speaker: chooses(r_true in R, wpp=1),
        speaker: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    listener: observes [speaker.u_said] is u
    listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
    return Pr[listener.r_pick == r]


def utterance_first[u: U, r: R]():
    listener: thinks[
        speaker: chooses(u_said in U, wpp=count(u_said)),
        speaker: chooses(r_true in R, wpp=denotes(u_said, r_true))
    ]
    listener: observes [speaker.u_said] is u
    listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
    return Pr[listener.r_pick == r]


def pragmatic[u: U, r: R]():
    listener: thinks[
        speaker: chooses(r_true in R, wpp=1),
        speaker: chooses(u_said in U, wpp=naive[u_said, r_true]())
    ]
    listener: observes [speaker.u_said] is u
    listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
    return Pr[listener.r_pick == r]


def speaker_knows[u: U, r: R]():
    speaker: knows(r)
    speaker: chooses(u_said in U, wpp=denotes(u_said, r))
    return Pr[speaker.u_said == u]


def nested_knows[u: U, r: R]():
    listener: knows(r)
    listener: thinks[
        speaker: knows(r),
        speaker: chooses(u_said in U, wpp=denotes(u_said, r))
    ]
    listener: chooses(u_guess in U, wpp=Pr[speaker.u_said == u_guess])
    return Pr[listener.u_guess == u]


def knows_other[u: U, r: R]():
    speaker: chooses(r_true in R, wpp=1)
    listener: knows(speaker.r_true)
    listener: thinks[
        speaker: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    listener: chooses(u_guess in U, wpp=Pr[speaker.u_said == u_guess])
    return Pr[listener.u_guess == u]


# A model comes after the models that it refers to.
MODELS = [naive, utterance_first, pragmatic, speaker_knows, nested_knows, knows_other]

if __name__ == "__main__":
    for f in MODELS:
        print(model(f))
