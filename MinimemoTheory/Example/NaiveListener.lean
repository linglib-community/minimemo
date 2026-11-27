/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Family
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Field.Defs

/-!
# The naive listener

This file writes the first model of the memo paper as a memo program with rational numbers,
computes its array, and proves that a second model returns the same array.

There are four utterances, *green*, *pink*, *square* and *round*, and three referents, a green
square, a green circle and a pink circle. A listener thinks that a speaker chooses a referent
uniformly and then an utterance uniformly among those that describe the referent. The listener
observes the utterance and chooses a referent with weight equal to its probability that the
speaker chose that referent. The model returns the probability that the listener chooses each
referent, in an array with an axis for the utterance and an axis for the referent.

The entry of the array at an utterance and a referent is the value of the denotation there divided
by the number of referents that the utterance describes.

In the second model the listener thinks that the speaker chooses the utterance first, with weight
the number of referents that it describes, and then a referent that it describes. The two
speakers choose in opposite orders. The listeners return the same array.

## Main definitions

* `Memo.NaiveListener.model`: the model, as a memo program.
* `Memo.NaiveListener.interpOf K`: the meaning of its domains and functions in a field `K`.
* `Memo.NaiveListener.utteranceFirst`: the model in which the speaker chooses the utterance first.
* `Memo.NaiveListener.rows`: the array that the model returns, as a list of rows.

## Main results

* `Memo.NaiveListener.rows_eq`: the entries are those of the array that the paper prints.
* `Memo.NaiveListener.rows_eq_denotes_div_count`: the entry at an utterance and a referent is the
  denotation there divided by the number of referents that the utterance describes.
* `Memo.NaiveListener.rows_utteranceFirst`: the two models return the same array.

## Implementation notes

The results hold by computation: the numbers are rational, and Lean evaluates the program of the
model. The model can also be run: `#eval Model.rows interp model` prints the array.

The paper writes the weight of an utterance as `1 if denotes(u, r) else 0`; here `denotes` has the
values one and zero.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

namespace Memo.NaiveListener

/-- The agents of the model. -/
inductive Agent
  | listener | speaker
  deriving DecidableEq

/-- The names of the choices of the model. The first two are its axes. -/
inductive Name
  | u | r | rTrue | uSaid | rPick
  deriving DecidableEq

/-- The names of the domains of the model: the utterances and the referents. -/
inductive Dom
  | U | R
  deriving DecidableEq

/-- The outside functions of the models: the denotation, and the number of referents that an
utterance describes. -/
inductive Fn : ℕ → Type
  | denotes : Fn 2
  | count : Fn 1
  deriving DecidableEq

/-- The utterances are *green*, *pink*, *square* and *round*, with the values 0 to 3. The
referents are a green square, a green circle and a pink circle, with the values 0 to 2. -/
def domOf (K : Type) [Field K] : Dom → Domain K
  | .U => ⟨4, fun j ↦ j⟩
  | .R => ⟨3, fun j ↦ j⟩

/-- The **denotation** has the value one when the utterance `u` describes the referent `r`, and
zero otherwise. -/
def denotesOf {K : Type} [Field K] [LinearOrder K] (u r : K) : K :=
  if (u = 0 ∧ (r = 0 ∨ r = 1)) ∨ (u = 1 ∧ r = 2) ∨ (u = 2 ∧ r = 0) ∨ (u = 3 ∧ (r = 1 ∨ r = 2))
  then 1 else 0

/-- The number of referents that the utterance `u` describes. -/
def countOf {K : Type} [Field K] [LinearOrder K] (u : K) : K :=
  denotesOf u 0 + denotesOf u 1 + denotesOf u 2

/-- The meaning of the outside functions in an ordered field. -/
def callOf (K : Type) [Field K] [LinearOrder K] : {k : ℕ} → Fn k → (Fin k → K) → K
  | _, .denotes, v => denotesOf (v 0) (v 1)
  | _, .count, v => countOf (v 0)

/-- The interpretation of the models in an ordered field. -/
def interpOf (K : Type) [Field K] [LinearOrder K] : Interp Dom Fn K :=
  .ofField (domOf K) (callOf K)

/-- The interpretation with rational numbers, which Lean evaluates. -/
abbrev interp : Interp Dom Fn ℚ := interpOf ℚ

/-- The domains with rational numbers. -/
abbrev dom : Dom → Domain ℚ := domOf ℚ

/-- The denotation with rational numbers. -/
abbrev denotes (u r : ℚ) : ℚ := denotesOf u r

/-- The number of referents that an utterance describes, with rational numbers. -/
abbrev count (u : ℚ) : ℚ := countOf u

/-- The model of the naive listener:
```
@memo def L[u: U, r: R]():
  listener: thinks[
    speaker: chooses(r_true in R, wpp=1),
    speaker: chooses(u_said in U, wpp=denotes(u_said, r_true)) ]
  listener: observes [speaker.u_said] is u
  listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
  return Pr[listener.r_pick == r]
```
-/
def model : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U (.call .denotes ![.choice .uSaid, .choice .rTrue])) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.prim .eq ![.query .speaker (.choice .rTrue), .choice .rPick]))
  ret := .expect (.prim .eq ![.query .listener (.choice .rPick), .choice .r])

/-- The array that the model returns, as a list of rows: one for each utterance, with an entry for
each referent. -/
def rows : List (List ℚ) := (Model.rows interp model).getD []

/-- The entries of the array are those that the paper prints for the naive listener: *green* and
*round* leave two referents equally likely, and *pink* and *square* pick out one. -/
theorem rows_eq :
    rows =
      [[1/2, 1/2, 0],
       [0,   0,   1],
       [1,   0,   0],
       [0,   1/2, 1/2]] := by
  decide +kernel

/-- The entry of the array at an utterance and a referent is the value of the denotation there
divided by the number of referents that the utterance describes. -/
theorem rows_eq_denotes_div_count :
    rows = (List.range 4).map fun u ↦ (List.range 3).map fun r ↦ denotes u r / count u := by
  decide +kernel

/-- The model in which the listener thinks that the speaker chooses the utterance first:
```
@memo def L'[u: U, r: R]():
  listener: thinks[
    speaker: chooses(u_said in U, wpp=count(u_said)),
    speaker: chooses(r_true in R, wpp=denotes(u_said, r_true)) ]
  listener: observes [speaker.u_said] is u
  listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
  return Pr[listener.r_pick == r]
```
-/
def utteranceFirst : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .uSaid .U (.call .count ![.choice .uSaid]) ;;
       .chooses .speaker .rTrue .R (.call .denotes ![.choice .uSaid, .choice .rTrue])) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.prim .eq ![.query .speaker (.choice .rTrue), .choice .rPick]))
  ret := .expect (.prim .eq ![.query .listener (.choice .rPick), .choice .r])

/-- The model in which the speaker chooses the utterance first returns the same array as the
model in which the speaker chooses the referent first. -/
theorem rows_utteranceFirst : Model.rows interp utteranceFirst = Model.rows interp model := by
  decide +kernel

end Memo.NaiveListener
