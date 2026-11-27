/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Example.Listener
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# A listener who reasons about itself

This file writes the recursive listener of memo as a family of models, one for each depth of
reasoning, and finds what the listener believes at every depth.

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
* `Memo.Recursive.entries_model`: the step from one depth to the next. Over a listener who gives
  the green square the probability `p` on hearing *green*, the listener gives it
  `2 * p / (3 * p + 1)`.
* `Memo.Recursive.greenSquare_eq`: at every depth `t`, the probability of the green square on
  hearing *green* is `2 ^ t / (3 * 2 ^ t - 1)`.
* `Memo.Recursive.greenSquare_strictAnti`, `Memo.Recursive.one_third_lt_greenSquare`: it falls
  with the depth and stays above one in three.
* `Memo.Recursive.tendsto_greenSquare`: it tends to one in three.

## Implementation notes

The model at a depth above zero is a listener whose speaker weighs an utterance by the probability
that the listener below gives the referent. The step is that of such a listener, where the array of
the listener below is a variable. The results at all depths follow by induction.
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

section Step

open Listener (arrayOf)

/-- The term for the weight of the utterance at a depth above zero: the denotation times the
probability that the listener below gives the referent. -/
def weightTerm : Term Dom Fn :=
  .rename [] (.op (.inl .mul) ![.op (.inr .denotes) ![.val 3 .U, .val 2 .R],
    .op (.inr .below) ![.val 3 .U, .val 2 .R]])

/-- The program of the model at a depth above zero is the program of a listener, with that
weight. -/
theorem program_eq : Model.program (model 1) = .ok (Listener.program weightTerm) := by
  program_rfl

/-- **The step from one depth to the next**: over a listener with the array `arrayOf p`, the model
at a depth above zero has the array `arrayOf (2 * p / (3 * p + 1))`. -/
theorem entries_model (p : ℚ) (hp : 0 < p) (hp1 : p < 1) :
    Model.entries (.ofField (domOf ℚ) (callOf ℚ [arrayOf p])) (model 1) =
      some (arrayOf (2 * p / (3 * p + 1))) := by
  rw [Model.entries, program_eq]
  show some ((Listener.program weightTerm).entries _) = _
  rw [Listener.entries_program (w := Listener.weight id (arrayOf p)) fun σ ↦ rfl,
    Listener.listener_weight id p hp one_pos (by simpa using hp1)]
  simp

theorem callOf_getLast (ts : List (List ℚ)) :
    @callOf ℚ _ _ ts = @callOf ℚ _ _ [ts.getLast?.getD []] := by
  funext k f v
  cases f <;> rfl

theorem model_succ (t : ℕ) : model (t + 1) = model 1 := by
  simp [model]

/-- The array at a depth above zero is the array of the model over the array one depth below. -/
theorem level_succ (t : ℕ) :
    level (t + 1) =
      (Model.entries (.ofField (domOf ℚ) (callOf ℚ [level t])) (model 1)).getD [] := by
  rw [level, Model.level, Model.levels, List.getLast?_concat, Option.getD_some, callOf_getLast,
    model_succ]
  rfl

/-- The array of the listener at every depth. -/
theorem level_eq (t : ℕ) : level t = arrayOf (2 ^ t / (3 * 2 ^ t - 1)) := by
  induction t with
  | zero => rw [level_zero]; norm_num [arrayOf]
  | succ t ih =>
    have h2 : (1 : ℚ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have h3 : (0 : ℚ) < 3 * 2 ^ t - 1 := by linarith
    rw [level_succ, ih, entries_model _ (by positivity) (by rw [div_lt_one h3]; linarith),
      Option.getD_some]
    congr 1
    rw [pow_succ]
    generalize (2 : ℚ) ^ t = a at h2 h3 ⊢
    have h4 : 6 * a - 1 ≠ 0 := by linarith
    have h5 : 3 * (a * 2) - 1 ≠ 0 := by linarith
    have e : 3 * (a / (3 * a - 1)) + 1 = (6 * a - 1) / (3 * a - 1) := by field_simp; ring
    rw [e, div_eq_div_iff (div_ne_zero h4 h3.ne') h5]
    field_simp
    ring

end Step

/-- The probability that the listener at depth `t` gives the green square on hearing *green*. -/
def greenSquare (t : ℕ) : ℚ := (level t).getD 0 0

/-- At every depth, the probability of the green square on hearing *green* is
`2 ^ t / (3 * 2 ^ t - 1)`: 1/2, 2/5, 4/11, 8/23, and so on. -/
theorem greenSquare_eq (t : ℕ) : greenSquare t = 2 ^ t / (3 * 2 ^ t - 1) := by
  rw [greenSquare, level_eq]
  rfl

/-- The probability of the green square after one more depth of reasoning. -/
theorem greenSquare_succ (t : ℕ) :
    greenSquare (t + 1) = 2 * greenSquare t / (3 * greenSquare t + 1) := by
  have h2 : (1 : ℚ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  rw [greenSquare_eq, greenSquare_eq, pow_succ]
  generalize (2 : ℚ) ^ t = a at h2 ⊢
  have h3 : 3 * a - 1 ≠ 0 := by linarith
  have h4 : 6 * a - 1 ≠ 0 := by linarith
  have h5 : 3 * (a * 2) - 1 ≠ 0 := by linarith
  have e : 3 * (a / (3 * a - 1)) + 1 = (6 * a - 1) / (3 * a - 1) := by field_simp; ring
  rw [e, eq_comm, div_eq_div_iff (div_ne_zero h4 h3) h5]
  field_simp
  ring

/-- Each further depth of reasoning makes the green square less likely on hearing *green*. -/
theorem greenSquare_strictAnti : StrictAnti greenSquare := by
  refine strictAnti_nat_of_succ_lt fun t ↦ ?_
  have h2 : (1 : ℚ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  rw [greenSquare_eq, greenSquare_eq, pow_succ, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- At every depth the green square stays more likely than one in three on hearing *green*. -/
theorem one_third_lt_greenSquare (t : ℕ) : 1 / 3 < greenSquare t := by
  have h2 : (1 : ℚ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  rw [greenSquare_eq, div_lt_div_iff₀ (by norm_num) (by linarith)]
  linarith

/-- As the depth of reasoning grows, the probability of the green square on hearing *green* tends
to one in three. -/
theorem tendsto_greenSquare :
    Filter.Tendsto (fun t ↦ (greenSquare t : ℝ)) Filter.atTop (nhds (1 / 3)) := by
  have h (t : ℕ) : (greenSquare t : ℝ) = 1 / (3 - (1 / 2 : ℝ) ^ t) := by
    have h2 : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have h3 : (3 : ℝ) * 2 ^ t - 1 ≠ 0 := by linarith
    have h4 : (3 : ℝ) - 1 / 2 ^ t ≠ 0 := by
      have : (1 : ℝ) / 2 ^ t ≤ 1 := by rw [div_le_one (by positivity)]; exact h2
      linarith
    rw [greenSquare_eq, div_pow, one_pow]
    push_cast
    field_simp
  simp_rw [h]
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 := (tendsto_const_nhds (x := (3 : ℝ))).sub h0
  rw [sub_zero] at h1
  exact (tendsto_const_nhds (x := (1 : ℝ))).div h1 (by norm_num)

end Memo.Recursive
