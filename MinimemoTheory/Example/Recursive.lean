/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Example.NaiveListener
public import MinimemoTheory.Denote
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

The step is proved on the meanings of the terms of the program, where the array of the listener
below is a variable; the stored tables have those meanings. The results at all depths follow by
induction.
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

/-- The array of a listener who, on hearing *green*, gives the green square the probability `p`,
and on hearing *round* gives the pink circle the probability `p`. -/
def arrayOf (p : ℚ) : List ℚ := [p, 1 - p, 0, 0, 0, 1, 1, 0, 0, 0, 1 - p, p]
/-- The interpretation in which the listener below has the array `arrayOf p`. -/
abbrev interpAt (p : ℚ) : Interp Dom Fn ℚ := .ofField (domOf ℚ) (callOf ℚ [arrayOf p])
/-- The sizes of the choices of the model at a depth above zero. -/
def size (i : ℕ) : ℕ := ([4, 3, 3, 4, 3] : List ℕ).getD i 1

/-- The weight of the referent. -/
def term₁ : Term Dom Fn := .rename [] (.lit 1)
/-- The speaker chooses a referent. -/
def term₂ : Term Dom Fn := Term.chooses 0 [2] (.ref 1)
/-- The weight of the utterance: the denotation times the probability that the listener below
gives the referent. -/
def term₃ : Term Dom Fn :=
  .rename [] (.op (.inl .mul) ![.op (.inr .denotes) ![.val 3 .U, .val 2 .R],
     .op (.inr .below) ![.val 3 .U, .val 2 .R]])
/-- The speaker chooses an utterance. -/
def term₄ : Term Dom Fn := Term.chooses 2 [3] (.ref 3)
/-- The listener observes the utterance. -/
def term₅ : Term Dom Fn := Term.observes 4 [2]
/-- The probability that the listener gives to a referent. -/
def term₆ : Term Dom Fn :=
  .rename [(3, 0)] (Term.expect 5 [2] (.op (.inl .eq) ![.rename [] (.val 2 .R), .val 4 .R]))
/-- The listener chooses a referent. -/
def term₇ : Term Dom Fn := Term.chooses 0 [4] (.ref 6)
/-- The probability that the listener chooses the referent of the second axis. -/
def termRet : Term Dom Fn :=
  Term.expect 7 [4] (.op (.inl .eq) ![.rename [(3, 0)] (.val 4 .R), .val 1 .R])
/-- The program of the model at a depth above zero, written out. -/
def program : Program Dom Fn :=
  ⟨[.U, .R, .R, .U, .R], [term₁, term₂, term₃, term₄, term₅, term₆, term₇], termRet, [0, 1]⟩

/-- The program of the model at a depth above zero is the one written out. -/
theorem program_eq : Model.program (model 1) = .ok program := by
  show Except.ok (Program.mk _ [_, _, _, _, _, _, _] _ _) =
    Except.ok (Program.mk _ [_, _, _, _, _, _, _] _ _)
  congr 1
  congr 1
  · repeat' first
      | (show Term.rename _ _ = Term.rename _ _; congr 1)
      | (show Term.op _ _ = Term.op _ _; congr 1)
      | (show Term.sum _ _ = Term.sum _ _; congr 1)
      | (show _ :: _ = _ :: _; congr 1)
      | (funext i; fin_cases i)
      | rfl
  · repeat' first
      | (show Term.rename _ _ = Term.rename _ _; congr 1)
      | (show Term.op _ _ = Term.op _ _; congr 1)
      | (show Term.sum _ _ = Term.sum _ _; congr 1)
      | (funext i; fin_cases i)
      | rfl

variable (p : ℚ)
/-- The meaning of the first table: the number one. -/
def stage₀ : (ℕ → ℕ) → ℚ := fun _ ↦ 1
/-- The meaning of the table of `term₁`. -/
def stage₁ := term₁.denote (interpAt p) size [stage₀]
/-- The meaning of the table of `term₂`. -/
def stage₂ := term₂.denote (interpAt p) size [stage₀, stage₁ p]
/-- The meaning of the table of `term₃`. -/
def stage₃ := term₃.denote (interpAt p) size [stage₀, stage₁ p, stage₂ p]
/-- The meaning of the table of `term₄`. -/
def stage₄ := term₄.denote (interpAt p) size [stage₀, stage₁ p, stage₂ p, stage₃ p]
/-- The meaning of the table of `term₅`. -/
def stage₅ := term₅.denote (interpAt p) size [stage₀, stage₁ p, stage₂ p, stage₃ p, stage₄ p]
/-- The meaning of the table of `term₆`. -/
def stage₆ :=
  term₆.denote (interpAt p) size [stage₀, stage₁ p, stage₂ p, stage₃ p, stage₄ p, stage₅ p]
/-- The meaning of the table of `term₇`. -/
def stage₇ := term₇.denote (interpAt p) size
  [stage₀, stage₁ p, stage₂ p, stage₃ p, stage₄ p, stage₅ p, stage₆ p]
/-- The meaning of the returned term. -/
def stageRet := termRet.denote (interpAt p) size
  [stage₀, stage₁ p, stage₂ p, stage₃ p, stage₄ p, stage₅ p, stage₆ p, stage₇ p]

theorem term_denote : program.term.denote (interpAt p) size [stage₀] = stageRet p := rfl

/-- The weight that the speaker gives to the utterance at position `u` for the referent at
position `r`. -/
def weight (u r : ℕ) : ℚ := denotesOf (u : ℚ) (r : ℚ) *
  Model.lookup [domOf ℚ .U, domOf ℚ .R] (arrayOf p) fun i ↦ if i = 0 then (u : ℚ) else r
/-- The probability that the listener thinks the speaker chooses the referent at position `r` and
then the utterance at position `u`. -/
def speaker (u r : ℕ) : ℚ :=
  1 / 3 * (weight p u r / (weight p 0 r + weight p 1 r + weight p 2 r + weight p 3 r))
/-- The probability that the listener gives to the referent at position `r` on hearing the
utterance at position `u`. -/
def posterior (u r : ℕ) : ℚ := speaker p u r / (speaker p u 0 + speaker p u 1 + speaker p u 2)
/-- The probability that the listener chooses the referent at position `r` on hearing the
utterance at position `u`. -/
def listener (u r : ℕ) : ℚ :=
  posterior p u r / (posterior p u 0 + posterior p u 1 + posterior p u 2)

theorem stage₁_eq (σ) : stage₁ p σ = 1 := rfl
theorem stage₃_eq (σ) : stage₃ p σ = weight p (σ 3) (σ 2) := rfl
theorem stage₂_eq (σ) : stage₂ p σ = 1 / 3 := by
  show stage₀ σ * (stage₁ p σ / ∑ j ∈ Finset.range 3, stage₁ p (Function.update σ 2 j)) = _
  simp [stage₁_eq, stage₀]
theorem stage₄_eq (σ) : stage₄ p σ = speaker p (σ 3) (σ 2) := by
  show stage₂ p σ * (stage₃ p σ / ∑ j ∈ Finset.range 4, stage₃ p (Function.update σ 3 j)) = _
  simp [Finset.sum_range_succ, stage₂_eq, stage₃_eq, speaker, Function.update]
theorem stage₅_eq (σ) : stage₅ p σ = posterior p (σ 3) (σ 2) := by
  show stage₄ p σ / ∑ j ∈ Finset.range 3, stage₄ p (Function.update σ 2 j) = _
  simp [Finset.sum_range_succ, stage₄_eq, posterior, Function.update]

theorem stage₆_eq (σ) (h : σ 4 < 3) : stage₆ p σ = posterior p (σ 0) (σ 4) := by
  show ∑ j ∈ Finset.range 3, (if (j : ℚ) = (σ 4 : ℚ) then 1 else 0) *
    stage₅ p (Function.update (fun i ↦ σ ((List.lookup i [(3, 0)]).getD i)) 2 j) = _
  obtain ⟨k, hk⟩ : ∃ k, σ 4 = k := ⟨_, rfl⟩
  rw [hk] at h ⊢
  interval_cases k <;> simp [Finset.sum_range_succ, stage₅_eq, Function.update, List.lookup]
theorem stage₇_eq (σ) (h : σ 4 < 3) : stage₇ p σ = listener p (σ 0) (σ 4) := by
  show stage₀ σ * (stage₆ p σ / ∑ j ∈ Finset.range 3, stage₆ p (Function.update σ 4 j)) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, stage₆_eq p σ h,
    stage₆_eq p _ (by simp), stage₆_eq p _ (by simp), stage₆_eq p _ (by simp)]
  simp [stage₀, listener, Function.update]
theorem stageRet_eq (σ) (h : σ 1 < 3) : stageRet p σ = listener p (σ 0) (σ 1) := by
  show ∑ j ∈ Finset.range 3,
    (if (((Function.update σ 4 j) ((List.lookup 4 [(3, 0)]).getD 4) : ℕ) : ℚ)
      = (Function.update σ 4 j 1 : ℚ) then 1 else 0) * stage₇ p (Function.update σ 4 j) = _
  obtain ⟨k, hk⟩ : ∃ k, σ 1 = k := ⟨_, rfl⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    stage₇_eq p _ (by simp), stage₇_eq p _ (by simp), stage₇_eq p _ (by simp), hk]
  rw [hk] at h
  interval_cases k <;> simp [Function.update, List.lookup, hk]

theorem index_utterance (u : ℕ) (h : u < 4) : (domOf ℚ .U).index (u : ℚ) = u := by
  interval_cases u <;> decide +kernel
theorem index_referent (r : ℕ) (h : r < 3) : (domOf ℚ .R).index (r : ℚ) = r := by
  interval_cases r <;> decide +kernel
theorem weight_eq (u r : ℕ) (hu : u < 4) (hr : r < 3) :
    weight p u r = denotesOf (u : ℚ) (r : ℚ) * (arrayOf p).getD (u * 3 + r) 0 := by
  show _ * (arrayOf p).getD
    ((0 * 4 + (domOf ℚ .U).index (u : ℚ)) * 3 + (domOf ℚ .R).index (r : ℚ)) 0 = _
  rw [index_utterance u hu, index_referent r hr, Nat.zero_mul, Nat.zero_add]

/-- **The step from one depth to the next**, on probabilities: if the listener below gives the
green square the probability `p` on hearing *green*, this listener gives it
`2 * p / (3 * p + 1)`. -/
theorem listener_eq (hp : 0 < p) (hp1 : p < 1) :
    [listener p 0 0, listener p 0 1, listener p 0 2, listener p 1 0, listener p 1 1, listener p 1 2,
     listener p 2 0, listener p 2 1, listener p 2 2,
     listener p 3 0, listener p 3 1, listener p 3 2] =
    arrayOf (2 * p / (3 * p + 1)) := by
  have h1 : 1 - p ≠ 0 := by linarith
  have h2 : 1 + p ≠ 0 := by linarith
  have h3 : 3 * p + 1 ≠ 0 := by linarith
  have h4 : p ≠ 0 := hp.ne'
  simp only [listener, posterior, speaker,
    weight_eq p _ _ (by norm_num : (0 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (0 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (0 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (1 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (1 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (1 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (2 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (2 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (2 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (3 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (3 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq p _ _ (by norm_num : (3 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3), arrayOf, denotesOf]
  norm_num
  have h5 : p + 1 ≠ 0 := by linarith
  have e : (1 - p) / (1 - p + (1 - p)) = 1 / 2 := by field_simp; ring
  rw [e]
  refine ⟨?_, ?_, h2, h5, ?_, ?_⟩ <;> field_simp <;> ring

theorem size_program : program.size (interpAt p) = size := by
  funext i
  match i with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | i + 5 => rfl

theorem inRange (a b : ℕ) (ha : a < 4) (hb : b < 3) :
    InRange size (Table.assign [0, 1] [a, b]) := fun i ↦ by
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | 2 | 4 => exact (by decide : 0 < 3)
  | 3 => exact (by decide : 0 < 4)
  | i + 5 => exact Nat.one_pos

theorem get_table (a b : ℕ) (ha : a < 4) (hb : b < 3) :
    (program.term.eval (interpAt p) size #[.const 1]).get size (Table.assign [0, 1] [a, b]) =
      listener p a b :=
  (Term.get_eval program.term _ _ Env.one _ (inRange a b ha hb)).trans (stageRet_eq p _ hb)

theorem entries_program : program.entries (interpAt p) =
    [listener p 0 0, listener p 0 1, listener p 0 2, listener p 1 0, listener p 1 1, listener p 1 2,
     listener p 2 0, listener p 2 1, listener p 2 2,
     listener p 3 0, listener p 3 1, listener p 3 2] := by
  rw [← get_table p 0 0 (by norm_num) (by norm_num),
    ← get_table p 0 1 (by norm_num) (by norm_num),
    ← get_table p 0 2 (by norm_num) (by norm_num),
    ← get_table p 1 0 (by norm_num) (by norm_num),
    ← get_table p 1 1 (by norm_num) (by norm_num),
    ← get_table p 1 2 (by norm_num) (by norm_num),
    ← get_table p 2 0 (by norm_num) (by norm_num),
    ← get_table p 2 1 (by norm_num) (by norm_num),
    ← get_table p 2 2 (by norm_num) (by norm_num),
    ← get_table p 3 0 (by norm_num) (by norm_num),
    ← get_table p 3 1 (by norm_num) (by norm_num),
    ← get_table p 3 2 (by norm_num) (by norm_num),
    Program.entries, Program.table, size_program]
  rfl

/-- **The step from one depth to the next**, on arrays: over a listener with the array
`arrayOf p`, the model at a depth above zero has the array `arrayOf (2 * p / (3 * p + 1))`. -/
theorem entries_model (hp : 0 < p) (hp1 : p < 1) :
    Model.entries (interpAt p) (model 1) = some (arrayOf (2 * p / (3 * p + 1))) := by
  rw [Model.entries, program_eq, ← listener_eq p hp hp1, ← entries_program]
  rfl

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
