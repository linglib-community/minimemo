"""Example models, written in memo.

U, R and denotes are taken from memo's RSA demo.
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


def weighted[u: U, r: R](w, k):
    speaker: knows(r)
    speaker: chooses(u_said in U, wpp=1 + w * denotes(u_said, r))
    return k * Pr[speaker.u_said == u] ** 2


def tempered[u: U, r: R](w):
    listener: thinks[
        speaker: chooses(r_true in R, wpp=1),
        speaker: chooses(u_said in U, wpp=weighted[u_said, r_true](w, 1))
    ]
    listener: observes [speaker.u_said] is u
    listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick] ** 3)
    return Pr[listener.r_pick == r]


def observes_that[u: U, r: R]():
    listener: knows(u)
    listener: thinks[
        speaker: chooses(r_true in R, wpp=1),
        speaker: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    listener: observes_that[speaker.u_said == u]
    listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
    return Pr[listener.r_pick == r]


def observes_event[u: U, r: R]():
    listener: knows(u)
    listener: thinks[
        speaker: chooses(r_true in R, wpp=1),
        speaker: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    listener: observes_event(wpp=1 + 3 * (speaker.u_said == u))
    listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
    return Pr[listener.r_pick == r]


def variance[u: U, r: R]():
    listener: knows(u)
    listener: thinks[
        speaker: chooses(r_true in R, wpp=1),
        speaker: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    listener: observes [speaker.u_said] is u
    return listener[Var[speaker.r_true]] + 0 * r


def chooses_two[u: U, r: R]():
    speaker: chooses(r_true in R, u_said in U, wpp=denotes(u_said, r_true) + 2 * (r_true == 5))
    return Pr[speaker.u_said == u, speaker.r_true == r]


def forgets[u: U, r: R]():
    speaker: chooses(r_true in R, wpp=1 + (r_true == 5))
    speaker: chooses(u_said in U, wpp=denotes(u_said, r_true))
    speaker: forgets_about(r_true)
    return Pr[speaker.u_said == u] + 0 * r


def maximize[u: U, r: R]():
    speaker: knows(r)
    speaker: chooses(u_said in U, to_maximize=denotes(u_said, r) + 2 * (u_said == 8))
    return Pr[speaker.u_said == u]


def snapshot[u: U, r: R]():
    speaker: chooses(r_true in R, wpp=1 + 2 * (r_true == 5))
    speaker: snapshots_self_as(past)
    speaker: chooses(u_said in U, wpp=denotes(u_said, past.r_true))
    return Pr[speaker.u_said == u] + 0 * r


def boolean_sum[u: U, r: R]():
    speaker: knows(r)
    speaker: chooses(u_said in U, wpp=1 + 2 * (denotes(u_said, r) + (u_said == 8)))
    return Pr[speaker.u_said == u]


def imagines[u: U, r: R]():
    listener: knows(u)
    listener: thinks[speaker: chooses(r_true in R, wpp=1)]
    listener: chooses(r_pick in R, wpp=imagine[
        speaker: chooses(u_said in U, wpp=denotes(u_said, r_true)),
        Pr[speaker.u_said == u, speaker.r_true == r_pick]
    ])
    return Pr[listener.r_pick == r]


def known_expectation[u: U, r: R]():
    speaker: knows(r)
    speaker: chooses(u_said in U, wpp=denotes(u_said, r))
    return E[speaker[E[r]] + (speaker.u_said == u)]


def repeated[u: U, r: R]():
    speaker: chooses(u_said in U, wpp=1)
    speaker: chooses(u_said in U, wpp=1)
    return Pr[speaker.u_said == u] + 0 * r


def three_deep[u: U, r: R]():
    alice: thinks[
        bob: thinks[
            carol: chooses(r_true in R, wpp=1 + (r_true == 9)),
            carol: chooses(u_said in U, wpp=denotes(u_said, r_true))
        ],
        bob: chooses(u_guess in U, wpp=Pr[carol.u_said == u_guess])
    ]
    alice: chooses(u_pick in U, wpp=Pr[bob.u_guess == u_pick])
    return Pr[alice.u_pick == u] + 0 * r


def two_observers[u: U, r: R]():
    alice: thinks[
        carol: chooses(r_true in R, wpp=1),
        carol: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    bob: thinks[
        carol: chooses(r_true in R, wpp=1 + 3 * (r_true == 10)),
        carol: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    alice: observes [carol.u_said] is u
    bob: observes [carol.u_said] is u
    return Pr[alice[Pr[carol.r_true == 10]] < bob[Pr[carol.r_true == 10]]] + 0 * r


def observes_agent[u: U, r: R]():
    carol: chooses(r_true in R, wpp=1)
    carol: chooses(u_said in U, wpp=denotes(u_said, r_true))
    alice: thinks[
        carol: chooses(r_true in R, wpp=1),
        carol: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    alice: observes [carol.u_said] is carol.u_said
    alice: chooses(r_pick in R, wpp=Pr[carol.r_true == r_pick])
    return Pr[alice.r_pick == r, carol.u_said == u]


def observes_two[u: U, r: R]():
    alice: thinks[
        carol: chooses(r_true in R, wpp=1),
        carol: chooses(u_said in U, wpp=denotes(u_said, r_true)),
        carol: chooses(u_again in U, wpp=denotes(u_again, r_true) + 2 * (u_again == u_said))
    ]
    alice: observes [carol.u_said] is u
    alice: chooses(u_next in U, wpp=Pr[carol.u_again == u_next])
    return E[alice.u_next == 8] + 0 * r


def spellings[u: U, r: R]():
    alice: given(r_true in R, uniformly)
    alice: draws(u_said in U, such_that=denotes(u_said, r_true))
    alice: assigned(u_low in U, to_minimize=abs(u_low - u_said) + 2 * (u_low == u_said))
    return Pr[alice.u_low == u, alice.r_true == r]


def arithmetic[u: U, r: R]():
    alice: chooses(x in R, wpp=(x - 4) / 2 + (x > 5) * 3 - (x != 9))
    alice: chooses(y in U, wpp=(1 if x == 9 else 2) * (y <= 2) + (y >= 4 and x < 10) + (y == 1 or x == 5))
    return E[-alice.x + alice.y ** 2] + Var[alice.y] * (u == 4) - r


def forgets_after_observing[u: U, r: R]():
    alice: thinks[
        carol: chooses(r_true in R, wpp=1),
        carol: chooses(u_said in U, wpp=denotes(u_said, r_true)),
        carol: chooses(u_again in U, wpp=denotes(u_again, r_true)),
        carol: forgets_about(r_true)
    ]
    alice: observes [carol.u_said] is u
    return alice[Pr[carol.u_again == 8]] + 0 * r


def snapshot_then_observes[u: U, r: R]():
    alice: thinks[
        carol: chooses(r_true in R, wpp=1),
        carol: chooses(u_said in U, wpp=denotes(u_said, r_true))
    ]
    alice: snapshots_self_as(past_alice)
    alice: observes [carol.u_said] is u
    return alice[past_alice[Pr[carol.r_true == 5]]] + 2 * alice[Pr[carol.r_true == 9]] + 0 * r


def event_in_thinks[u: U, r: R]():
    alice: thinks[
        bob: thinks[carol: chooses(r_true in R, wpp=1)],
        bob: observes_event(wpp=1 + 4 * (carol.r_true == 9)),
        bob: chooses(r_pick in R, wpp=Pr[carol.r_true == r_pick])
    ]
    return alice[Pr[bob.r_pick == 9]] + 0 * u + 0 * r


def nested_imagine[u: U, r: R]():
    alice: knows(u)
    alice: chooses(r_pick in R, wpp=imagine[
        bob: chooses(r_true in R, wpp=1 + (r_true == 9)),
        bob: chooses(u_said in U, wpp=denotes(u_said, r_true)),
        imagine[
            bob: chooses(extra in R, wpp=1 + (extra == r_true)),
            Pr[bob.extra == 5, bob.u_said == u, bob.r_true == r_pick]
        ]
    ])
    return Pr[alice.r_pick == r]


def uncertain_weight[u: U, r: R]():
    alice: thinks[carol: chooses(r_true in R, wpp=1)]
    alice: chooses(r_pick in R, wpp=carol.r_true == r_pick)
    return Pr[alice.r_pick == r] + 0 * u


def observes_known[u: U, r: R]():
    alice: thinks[carol: chooses(r_true in R, wpp=1)]
    alice: observes [carol.r_true] is r
    alice: observes [carol.r_true] is r
    return alice[Pr[carol.r_true == 5]] + 0 * u


def wrong_domain[u: U, r: R]():
    alice: thinks[carol: chooses(r_true in R, wpp=1)]
    alice: observes [carol.r_true] is u
    return alice[Pr[carol.r_true == 5]] + 0 * r


def unknown_choice[u: U, r: R]():
    alice: chooses(x in R, wpp=1)
    return Pr[alice.y == r] + 0 * u


def asks_uncertain[u: U, r: R]():
    alice: thinks[carol: chooses(r_true in R, wpp=1)]
    return alice[carol.r_true] + 0 * u + 0 * r


def level[u: U, r: R](t):
    listener: thinks[
        speaker: chooses(r_true in R, wpp=1),
        speaker: chooses(u_said in U, wpp=denotes(u_said, r_true) * (
            1 if t == 0 else level[u_said, r_true](t - 1)))
    ]
    listener: observes [speaker.u_said] is u
    listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
    return Pr[listener.r_pick == r]


def level_one[u: U, r: R]():
    return level[u, r](1)


def fib[u: U, r: R](n):
    return (1 if n < 2 else fib[u, r](n - 1) + fib[u, r](n - 2)) + 0 * u + 0 * r


def halving[u: U, r: R](t, w):
    speaker: knows(r)
    speaker: chooses(u_said in U, wpp=1 + w * denotes(u_said, r) * (
        1 if t <= 0 else halving[u_said, r](t - 1, w / 2)))
    return Pr[speaker.u_said == u]


# A model comes after the models that it refers to.
MODELS = [naive, utterance_first, pragmatic, speaker_knows, nested_knows, knows_other,
          weighted, tempered, observes_that, observes_event, variance, chooses_two, forgets,
          maximize, snapshot, boolean_sum, imagines, known_expectation, repeated,
          three_deep, two_observers, observes_agent, observes_two, spellings, arithmetic,
          forgets_after_observing, snapshot_then_observes, event_in_thinks, nested_imagine,
          uncertain_weight, observes_known, wrong_domain, unknown_choice, asks_uncertain,
          level, level_one, fib, halving]

# Parameter values for the comparison with memo.
ARGS = {"weighted": (0.5, 3), "tempered": (0.25,), "level": (2,), "fib": (6,),
        "halving": (3, 0.5)}

if __name__ == "__main__":
    for f in MODELS:
        print(model(f))
