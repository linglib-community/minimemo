/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Example.Listener
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.Field.Basic

/-!
# The Rational Speech Acts listener, at every depth

This file writes memo's model of the Rational Speech Acts framework as a family of models over the
real numbers, one for each depth of reasoning, and finds what the listener believes at every
depth.

At depth zero the listener thinks that the speaker chooses a referent uniformly and then an
utterance among those that describe it. At a greater depth the listener thinks that the speaker
weighs each such utterance by the exponential of `β` times the probability that the listener one
depth below gives the referent on hearing it.

On hearing *green*, the listener at depth zero finds the green square and the green circle equally
likely. One more depth of reasoning takes the probability `p` of the green square to
`2 / (3 + exp (β * (1 - p)))`.

## Main definitions

* `Memo.RSA.model t`: the listener at depth `t`, as a memo program that refers to the listener
  below.
* `Memo.RSA.level β t`: the array of the listener at depth `t`, with real numbers.
* `Memo.RSA.prob β t`: the probability that the recursion gives the green square at depth `t`.

## Main results

* `Memo.RSA.level_eq`: the array of the listener at every depth.
* `Memo.RSA.greenSquare_eq`: on hearing *green*, the listener at depth `t` gives the green square
  the probability `prob β t`.
* `Memo.RSA.prob_succ`: the step `p ↦ 2 / (3 + exp (β * (1 - p)))`.
* `Memo.RSA.prob_zero_left`: when `β` is zero, the probability is one half at every depth.
* `Memo.RSA.prob_le_half`: when `β` is not negative, the green square is at most as likely as the
  green circle at every depth.

## Implementation notes

The real numbers are not computed with: the results are proved on the meaning of the program, in
which the array of the listener below is a variable. The same model is run in floating point,
against memo, by `scripts/difftest.py examples_exp`.

The parameter `β` is an outside function of no arguments, whose value the interpretation gives.
So the model is one program for every `β`, and `β` is any real number.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

namespace Memo.RSA

open NaiveListener (Agent Name Dom domOf denotesOf)
open Listener (arrayOf)

/-- The outside functions of the model: the denotation, the listener one depth below, the
exponential, and the parameter `β`. -/
inductive Fn : ℕ → Type
  | denotes : Fn 2
  | below : Fn 2
  | exp : Fn 1
  | beta : Fn 0
  deriving DecidableEq

/-- The listener at depth `t`:
```
@memo def L[u: U, r: R](beta, t):
  listener: thinks[
    speaker: given(r in R, wpp=1),
    speaker: chooses(u in U, wpp=
      denotes(u, r) * (1 if t == 0 else exp(beta * L[u, r](beta, t - 1)))) ]
  listener: observes [speaker.u] is u
  listener: chooses(r in R, wpp=Pr[speaker.r == r])
  return Pr[listener.r == r]
```
-/
def model (t : ℕ) : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U
        (.prim .mul ![.call .denotes ![.choice .uSaid, .choice .rTrue],
          if t = 0 then .lit 1
          else .call .exp ![.prim .mul ![.call .beta ![],
            .call .below ![.choice .uSaid, .choice .rTrue]]]])) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.prim .eq ![.query .speaker (.choice .rTrue), .choice .rPick]))
  ret := .expect (.prim .eq ![.query .listener (.choice .rPick), .choice .r])

/-- The meaning of the outside functions in the real numbers, for the parameter `β`, when `ts`
holds the arrays of the listeners at the depths below: the listener one depth below is the last of
them. -/
noncomputable def callOf (β : ℝ) (ts : List (List ℝ)) : {k : ℕ} → Fn k → (Fin k → ℝ) → ℝ
  | _, .denotes, v => denotesOf (v 0) (v 1)
  | _, .below, v =>
    Model.lookup [domOf ℝ .U, domOf ℝ .R] (ts.getLast?.getD []) fun i ↦ if i = 0 then v 0 else v 1
  | _, .exp, v => Real.exp (v 0)
  | _, .beta, _ => β

/-- The array of the listener at depth `t`, with real numbers: one entry for each utterance and
referent, in row-major order. -/
noncomputable def level (β : ℝ) (t : ℕ) : List ℝ := Model.level (domOf ℝ) (callOf β) model t

/-- The probability that the recursion gives the green square on hearing *green*, at depth `t`. -/
noncomputable def prob (β : ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | t + 1 => 2 * Real.exp (β * prob β t) / (3 * Real.exp (β * prob β t) + Real.exp (β * 1))

section Step

/-- The term for the weight of the utterance at depth zero: the denotation. -/
def weightTerm₀ : Term Dom Fn :=
  .rename [] (.op (.inl .mul) ![.op (.inr .denotes) ![.val 3 .U, .val 2 .R], .lit 1])

/-- The term for the weight of the utterance at a depth above zero: the denotation times the
exponential of `β` times the probability that the listener below gives the referent. -/
def weightTerm : Term Dom Fn :=
  .rename [] (.op (.inl .mul) ![.op (.inr .denotes) ![.val 3 .U, .val 2 .R],
    .op (.inr .exp) ![.op (.inl .mul) ![.op (.inr .beta) ![],
      .op (.inr .below) ![.val 3 .U, .val 2 .R]]]])

theorem program_zero : Model.program (model 0) = .ok (Listener.program weightTerm₀) := by
  program_rfl

theorem program_one : Model.program (model 1) = .ok (Listener.program weightTerm) := by
  program_rfl

/-- The listener at depth zero gives the green square the probability one half on hearing
*green*. -/
theorem entries_zero (β : ℝ) (ts : List (List ℝ)) :
    Model.entries (.ofField (domOf ℝ) (callOf β ts)) (model 0) = some (arrayOf (1 / 2)) := by
  rw [Model.entries, program_zero]
  show some ((Listener.program weightTerm₀).entries _) = _
  rw [Listener.entries_program (w := Listener.weight (fun _ ↦ 1) (arrayOf 0)) fun σ ↦ by
      show _ * ((1 : ℚ) : ℝ) = _ * 1
      rw [Rat.cast_one]
      rfl,
    Listener.listener_weight (fun _ ↦ 1) 0 one_pos one_pos one_pos]
  norm_num

/-- **The step from one depth to the next**: over a listener with the array `arrayOf p`, the model
at a depth above zero has the array of the probability
`2 * exp (β * p) / (3 * exp (β * p) + exp β)`. -/
theorem entries_one (β p : ℝ) :
    Model.entries (.ofField (domOf ℝ) (callOf β [arrayOf p])) (model 1) =
      some (arrayOf (2 * Real.exp (β * p) / (3 * Real.exp (β * p) + Real.exp (β * 1)))) := by
  rw [Model.entries, program_one]
  show some ((Listener.program weightTerm).entries _) = _
  rw [Listener.entries_program (w := Listener.weight (fun x ↦ Real.exp (β * x)) (arrayOf p))
      fun σ ↦ rfl,
    Listener.listener_weight (fun x ↦ Real.exp (β * x)) p (Real.exp_pos _) (Real.exp_pos _)
      (Real.exp_pos _)]

theorem callOf_getLast (β : ℝ) (ts : List (List ℝ)) :
    @callOf β ts = @callOf β [ts.getLast?.getD []] := by
  funext k f v
  cases f <;> rfl

theorem model_succ (t : ℕ) : model (t + 1) = model 1 := by
  simp [model]

theorem level_zero (β : ℝ) : level β 0 = arrayOf (1 / 2) := by
  rw [level, Model.level, Model.levels, List.getLast?_concat, Option.getD_some, entries_zero,
    Option.getD_some]

theorem level_succ (β : ℝ) (t : ℕ) :
    level β (t + 1) =
      (Model.entries (.ofField (domOf ℝ) (callOf β [level β t])) (model 1)).getD [] := by
  rw [level, Model.level, Model.levels, List.getLast?_concat, Option.getD_some, callOf_getLast,
    model_succ]
  rfl

end Step

/-- The array of the listener at every depth. -/
theorem level_eq (β : ℝ) (t : ℕ) : level β t = arrayOf (prob β t) := by
  induction t with
  | zero => exact level_zero β
  | succ t ih => rw [level_succ, ih, entries_one, Option.getD_some, prob]

/-- On hearing *green*, the listener at depth `t` gives the green square the probability
`prob β t`. -/
theorem greenSquare_eq (β : ℝ) (t : ℕ) : (level β t).getD 0 0 = prob β t := by
  rw [level_eq]
  rfl

/-- One more depth of reasoning takes the probability `p` of the green square to
`2 / (3 + exp (β * (1 - p)))`. -/
theorem prob_succ (β : ℝ) (t : ℕ) :
    prob β (t + 1) = 2 / (3 + Real.exp (β * (1 - prob β t))) := by
  have h : Real.exp (β * (1 - prob β t)) = Real.exp (β * 1) / Real.exp (β * prob β t) := by
    rw [← Real.exp_sub]
    ring_nf
  have hp := Real.exp_pos (β * prob β t)
  rw [prob, h]
  field_simp

/-- When `β` is zero the speaker does not attend to the listener, and the probability of the green
square is one half at every depth. -/
theorem prob_zero_left (t : ℕ) : prob 0 t = 1 / 2 := by
  cases t with
  | zero => rfl
  | succ t => rw [prob_succ]; norm_num

/-- When `β` is not negative, the green square is at most as likely as the green circle on hearing
*green*, at every depth. -/
theorem prob_le_half {β : ℝ} (hβ : 0 ≤ β) (t : ℕ) : 0 < prob β t ∧ prob β t ≤ 1 / 2 := by
  induction t with
  | zero => exact ⟨by norm_num [prob], le_of_eq rfl⟩
  | succ t ih =>
    have h1 : 1 ≤ Real.exp (β * (1 - prob β t)) :=
      Real.one_le_exp (mul_nonneg hβ (by linarith [ih.2]))
    rw [prob_succ]
    exact ⟨by positivity, by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith⟩

end Memo.RSA
