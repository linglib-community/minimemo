/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Example.NaiveListener

/-!
# A listener who reasons about itself

This file writes the recursive listener of memo as a family of models, one for each depth of
reasoning, and computes what the listener believes at the first depths.

At depth zero the listener thinks that the speaker chooses a referent uniformly and then an
utterance among those that describe it. At a greater depth the listener thinks that the speaker
weighs each such utterance by the probability that the listener one depth below gives the
referent on hearing it. This is the recursion of memo's model of the Rational Speech Acts
framework, with that probability as the weight in place of its exponential, so that the numbers
are rational.

On hearing *green*, the listener at depth zero finds the green square and the green circle equally
likely. At each greater depth it finds the green square less likely: a speaker who meant the square
would have said *square*.

## Main definitions

* `Memo.Recursive.model t`: the listener at depth `t`, as a memo program that refers to the
  listener below.
* `Memo.Recursive.level t`: the array of the listener at depth `t`.

## Main results

* `Memo.Recursive.level_zero`: the listener at depth zero is the naive listener.
* `Memo.Recursive.level_one`: the listener at depth one is the pragmatic listener.
* `Memo.Recursive.greenSquare_eq`: the probability of the green square on hearing *green* is
  `2 ^ t / (3 * 2 ^ t - 1)`, at the depths zero to eight.
* `Memo.Recursive.greenSquare_anti`: it falls with the depth and stays above one in three, at
  those depths.

## TODO

The formula `2 ^ t / (3 * 2 ^ t - 1)` should hold at every depth, so that the probability falls
to one in three and no further. The results here are computed depth by depth. A proof for all
depths needs the array at depth `t + 1` as a function of a symbolic array at depth `t`, which
evaluation does not give.
-/

@[expose] public section

namespace Memo.Recursive

open NaiveListener (Agent Name Dom domOf denotesOf)

/-- The outside functions of the model: the denotation, and the listener one depth below. -/
inductive Fn : ℕ → Type
  | denotes : Fn 2
  | below : Fn 2
  deriving DecidableEq

/-- The listener at depth `t`:
```
@memo def L[u: U, r: R](t):
  listener: thinks[
    speaker: chooses(r_true in R, wpp=1),
    speaker: chooses(u_said in U, wpp=
      denotes(u_said, r_true) * (1 if t == 0 else L[u_said, r_true](t - 1))) ]
  listener: observes [speaker.u_said] is u
  listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
  return Pr[listener.r_pick == r]
```
-/
def model (t : ℕ) : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U
        (.prim .mul ![.call .denotes ![.choice .uSaid, .choice .rTrue],
          if t = 0 then .lit 1 else .call .below ![.choice .uSaid, .choice .rTrue]])) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.prim .eq ![.query .speaker (.choice .rTrue), .choice .rPick]))
  ret := .expect (.prim .eq ![.query .listener (.choice .rPick), .choice .r])

/-- The meaning of the outside functions in an ordered field, when `ts` holds the arrays of the
listeners at the depths below: the listener one depth below is the last of them. -/
def callOf (K : Type) [Field K] [LinearOrder K] (ts : List (List K)) :
    {k : ℕ} → Fn k → (Fin k → K) → K
  | _, .denotes, v => denotesOf (v 0) (v 1)
  | _, .below, v =>
    Model.lookup [domOf K .U, domOf K .R] (ts.getLast?.getD []) fun i ↦ if i = 0 then v 0 else v 1

/-- The array of the listener at depth `t`, with rational numbers: one entry for each utterance
and referent, in row-major order. -/
def level (t : ℕ) : List ℚ := Model.level (domOf ℚ) (callOf ℚ) model t

/-- The listener at depth zero is the naive listener. -/
theorem level_zero : level 0 = [1/2, 1/2, 0, 0, 0, 1, 1, 0, 0, 0, 1/2, 1/2] := by
  decide +kernel

/-- The listener at depth one is the pragmatic listener: on hearing *green* it gives the green
circle the probability 3/5. -/
theorem level_one : level 1 = [2/5, 3/5, 0, 0, 0, 1, 1, 0, 0, 0, 3/5, 2/5] := by
  decide +kernel

/-- The probability that the listener at depth `t` gives the green square on hearing *green*. -/
def greenSquare (t : ℕ) : ℚ := (level t).getD 0 0

/-- At the depths zero to eight, the probability of the green square on hearing *green* is
`2 ^ t / (3 * 2 ^ t - 1)`: 1/2, 2/5, 4/11, 8/23, and so on. -/
theorem greenSquare_eq :
    ∀ t ∈ List.range 9, greenSquare t = 2 ^ t / (3 * 2 ^ t - 1) := by
  decide +kernel

/-- At the depths zero to eight, each further depth of reasoning makes the green square less
likely on hearing *green*, and it stays more likely than one in three. -/
theorem greenSquare_anti :
    ∀ t ∈ List.range 8, greenSquare (t + 1) < greenSquare t ∧ 1 / 3 < greenSquare (t + 1) := by
  decide +kernel

end Memo.Recursive
