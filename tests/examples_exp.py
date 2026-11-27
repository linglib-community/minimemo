"""Example models that use the exponential, written in memo. They are run in floating point.

U, R, denotes and the first model are taken from memo's RSA demo.
"""
import jax

from examples import R, U, denotes


def L[u: U, r: R](beta, t):
    listener: thinks[
        speaker: given(r in R, wpp=1),
        speaker: chooses(u in U, wpp=
            denotes(u, r) * (1 if t == 0 else exp(beta * L[u, r](beta, t - 1))))
    ]
    listener: observes [speaker.u] is u
    listener: chooses(r in R, wpp=Pr[speaker.r == r])
    return Pr[listener.r == r]


def L_deep[u: U, r: R](beta):
    return L[u, r](beta, 3)


@jax.jit
def utility(r):
    return 1.0 * r


def softmax[r: R](beta):
    alice: chooses(r in R, wpp=exp(beta * utility(r)))
    return Pr[alice.r == r]


def log_weight[r: R]():
    alice: chooses(r in R, wpp=exp(2 * log(utility(r))))
    return Pr[alice.r == r]


def power[r: R]():
    alice: chooses(r in R, wpp=utility(r) ** 1.5)
    return Pr[alice.r == r]


MODELS = [L, L_deep, softmax, log_weight, power]
ARGS = {"L": (1.74, 1), "L_deep": (1.0,), "softmax": (0.1,)}
