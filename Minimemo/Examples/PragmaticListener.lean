/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Examples.NaiveListener
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# The pragmatic listener

This file writes a second listener as a memo program and compares it with the naive listener.

The pragmatic listener thinks that the speaker reasons about a listener. Its speaker chooses a
referent uniformly, and then an utterance with weight the probability that the naive listener
gives that referent at that utterance. A speaker who means the green square prefers *square* to
*green*, since *square* picks the square out. So when the pragmatic listener hears *green* it
gives the green circle the probability 3/5 and the green square 2/5, where the naive listener
gives each of them 1/2.

The two models are compared on responses to *green*. The likelihood of a data set, in which `a`
listeners pick the green square and `b` pick the green circle, is the product of the probabilities
that a model gives these picks. The pragmatic listener has the greater likelihood on every data
set in which at least two thirds of the picks are the circle, and on the counts 65 and 115 that
the demonstration of this model in the memo repository uses.

## Main definitions

* `Memo.PragmaticListener.model`: the model, as a memo program.
* `Memo.PragmaticListener.rows`: the array that the model returns, as a list of rows.
* `Memo.PragmaticListener.likelihood z a b`: the likelihood under the array `z` of `a` picks of
  the green square and `b` picks of the green circle at *green*.

## Main results

* `Memo.PragmaticListener.rows_eq`: the array that the model returns.
* `Memo.PragmaticListener.likelihood_lt`: if at least two thirds of the picks are the circle, the
  pragmatic listener has the greater likelihood.
* `Memo.PragmaticListener.likelihood_lt_demo`: the pragmatic listener has the greater likelihood
  on 65 picks of the square and 115 of the circle.

## Implementation notes

In the demonstration in the memo repository the weight of an utterance is the exponential of a
multiple of the naive listener's probability. Here it is that probability, so that the numbers are
rational and Lean evaluates the model.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

namespace Memo.PragmaticListener

open NaiveListener (Agent Name Dom domOf denotesOf countOf)

/-- The probability that the naive listener gives the referent `r` at the utterance `u`. -/
def naiveOf {K : Type} [Field K] [LinearOrder K] (u r : K) : K := denotesOf u r / countOf u

/-- That probability with rational numbers. -/
abbrev naive (u r : ℚ) : ℚ := naiveOf u r

/-- The function `naive` gives the entries of the array of the naive listener. -/
theorem rows_naive :
    NaiveListener.rows = (List.range 4).map fun u ↦ (List.range 3).map fun r ↦ naive u r :=
  NaiveListener.rows_eq_denotes_div_count

/-- The outside function of the model: the probability that the naive listener gives. -/
inductive Fn : ℕ → Type
  | naive : Fn 2
  deriving DecidableEq

/-- The meaning of the outside function. -/
def callOf (K : Type) [Field K] [LinearOrder K] : {k : ℕ} → Fn k → (Fin k → K) → K
  | _, .naive, v => naiveOf (v 0) (v 1)

/-- The interpretation of the model in an ordered field. -/
def interpOf (K : Type) [Field K] [LinearOrder K] : Interp Dom Fn K :=
  .ofField (domOf K) (callOf K)

/-- The interpretation with rational numbers, which Lean evaluates. -/
abbrev interp : Interp Dom Fn ℚ := interpOf ℚ

/-- The model of the pragmatic listener:
```
@memo def L1[u: U, r: R]():
  listener: thinks[
    speaker: chooses(r_true in R, wpp=1),
    speaker: chooses(u_said in U, wpp=L[u_said, r_true]()) ]
  listener: observes [speaker.u_said] is u
  listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
  return Pr[listener.r_pick == r]
```
where `L` is the model of the naive listener. -/
def model : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U (.call .naive ![.choice .uSaid, .choice .rTrue])) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.prim .eq ![.query .speaker (.choice .rTrue), .choice .rPick]))
  ret := .expect (.prim .eq ![.query .listener (.choice .rPick), .choice .r])

/-- The array that the model returns, as a list of rows: one for each utterance, with an entry for
each referent. -/
def rows : List (List ℚ) := (Model.rows interp model).getD []

/-- The array of the pragmatic listener: at *green* it gives the green circle the probability 3/5
and the green square 2/5, and at *round* it gives the green circle 3/5 and the pink circle 2/5. -/
theorem rows_eq :
    rows =
      [[2/5, 3/5, 0],
       [0,   0,   1],
       [1,   0,   0],
       [0,   3/5, 2/5]] := by
  decide +kernel

/-- The **likelihood** under an array of a data set of responses to *green*, in which `a`
listeners pick the green square and `b` pick the green circle. -/
def likelihood (z : List (List ℚ)) (a b : ℕ) : ℚ :=
  (z.getD 0 []).getD 0 0 ^ a * (z.getD 0 []).getD 1 0 ^ b

theorem likelihood_naive (a b : ℕ) :
    likelihood NaiveListener.rows a b = (1 / 2) ^ a * (1 / 2) ^ b := by
  rw [likelihood, NaiveListener.rows_eq]
  rfl

theorem likelihood_rows (a b : ℕ) : likelihood rows a b = (2 / 5) ^ a * (3 / 5) ^ b := by
  rw [likelihood, rows_eq]
  rfl

/-- If at least two thirds of the listeners who hear *green* pick the green circle, the pragmatic
listener has a greater likelihood than the naive listener. -/
theorem likelihood_lt {a b : ℕ} (h : 2 * a ≤ b) (hb : 0 < b) :
    likelihood NaiveListener.rows a b < likelihood rows a b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have e₁ : (1 / 2 : ℚ) ^ a * (1 / 2) ^ (2 * a + k) = (1 / 8) ^ a * (1 / 2) ^ k := by
    rw [pow_add, pow_mul, ← mul_assoc, ← mul_pow]; norm_num
  have e₂ : (2 / 5 : ℚ) ^ a * (3 / 5) ^ (2 * a + k) = (18 / 125) ^ a * (3 / 5) ^ k := by
    rw [pow_add, pow_mul, ← mul_assoc, ← mul_pow]; norm_num
  rw [likelihood_naive, likelihood_rows, e₁, e₂]
  have hk : (1 / 2 : ℚ) ^ k ≤ (3 / 5) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simpa using pow_lt_pow_left₀ (by norm_num : (1 / 2 : ℚ) < 3 / 5) (by norm_num)
      (by omega : k ≠ 0)
  · exact mul_lt_mul (pow_lt_pow_left₀ (by norm_num) (by norm_num) ha.ne') hk (by positivity)
      (by positivity)

/-- The pragmatic listener has a greater likelihood than the naive listener on 65 picks of the
green square and 115 picks of the green circle, the counts that the demonstration of this model in
the memo repository uses. -/
theorem likelihood_lt_demo : likelihood NaiveListener.rows 65 115 < likelihood rows 65 115 := by
  decide +kernel

end Memo.PragmaticListener
