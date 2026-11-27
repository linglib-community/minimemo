/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Example.NaiveListener
public import MinimemoTheory.Denote
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A listener and the speaker it has in mind, for any weight of the utterance

A listener thinks that a speaker chooses a referent uniformly and then an utterance with some
weight. The listener observes the utterance and chooses a referent with weight equal to its
probability that the speaker chose that referent. This file writes out the program of such a
model, with the term for the weight of the utterance left open, and finds its array as a function
of that weight.

The naive listener, the pragmatic listener and the listeners of the Rational Speech Acts framework
at any depth are such models. They differ in the weight alone.

## Main definitions

* `Memo.Listener.program wt`: the program, with `wt` the term for the weight of the utterance.
* `Memo.Listener.listener w u r`: the probability that the listener chooses the referent at
  position `r` on hearing the utterance at position `u`, when the weight is `w`.

## Main results

* `Memo.Listener.entries_program`: the array of the program has the entries `listener w u r`.
-/

@[expose] public section

namespace Memo.Listener

open NaiveListener (Dom domOf denotesOf)

/-- Closes the goal that the program of a model is a program that is written out, when the two
have the same terms. The program written out is on the left while the terms are compared, so that
a term of another form is told apart without computing the program of the model. -/
macro "program_rfl" : tactic => `(tactic|
  (symm
   show Except.ok (Program.mk _ [_, _, _, _, _, _, _] _ _) =
      Except.ok (Program.mk _ [_, _, _, _, _, _, _] _ _)
   congr 1
   congr 1 <;>
    repeat' first
      | (show Term.rename _ _ = Term.rename _ _; congr 1)
      | (show Term.op _ _ = Term.op _ _; congr 1)
      | (show Term.sum _ _ = Term.sum _ _; congr 1)
      | (show _ :: _ = _ :: _; congr 1)
      | (funext i; fin_cases i)
      | rfl))

variable {F : ℕ → Type}

/-- The sizes of the choices of the model: the axes `0` and `1`, the referent `2` and the
utterance `3` of the speaker, and the referent `4` that the listener chooses. -/
def size (i : ℕ) : ℕ := ([4, 3, 3, 4, 3] : List ℕ).getD i 1

/-- The weight of the referent. -/
def term₁ : Term Dom F := .rename [] (.lit 1)
/-- The speaker chooses a referent. -/
def term₂ : Term Dom F := Term.chooses 0 [2] (.ref 1)
/-- The speaker chooses an utterance. -/
def term₄ : Term Dom F := Term.chooses 2 [3] (.ref 3)
/-- The listener observes the utterance. -/
def term₅ : Term Dom F := Term.observes 4 [2]
/-- The probability that the listener gives to a referent. -/
def term₆ : Term Dom F :=
  .rename [(3, 0)] (Term.expect 5 [2] (.op (.inl .eq) ![.rename [] (.val 2 .R), .val 4 .R]))
/-- The listener chooses a referent. -/
def term₇ : Term Dom F := Term.chooses 0 [4] (.ref 6)
/-- The probability that the listener chooses the referent of the second axis. -/
def termRet : Term Dom F :=
  Term.expect 7 [4] (.op (.inl .eq) ![.rename [(3, 0)] (.val 4 .R), .val 1 .R])

/-- The program of the model, with `wt` the term for the weight of the utterance. -/
def program (wt : Term Dom F) : Program Dom F :=
  ⟨[.U, .R, .R, .U, .R], [term₁, term₂, wt, term₄, term₅, term₆, term₇], termRet, [0, 1]⟩

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

section Weight

variable (w : ℕ → ℕ → K)

/-- The probability that the listener thinks the speaker chooses the referent at position `r` and
then the utterance at position `u`. -/
def speaker (u r : ℕ) : K := 1 / 3 * (w u r / (w 0 r + w 1 r + w 2 r + w 3 r))
/-- The probability that the listener gives to the referent at position `r` on hearing the
utterance at position `u`. -/
def posterior (u r : ℕ) : K := speaker w u r / (speaker w u 0 + speaker w u 1 + speaker w u 2)
/-- The probability that the listener chooses the referent at position `r` on hearing the
utterance at position `u`. -/
def listener (u r : ℕ) : K :=
  posterior w u r / (posterior w u 0 + posterior w u 1 + posterior w u 2)

end Weight

variable (call : {k : ℕ} → F k → (Fin k → K) → K) (wt : Term Dom F)

/-- The interpretation of the model: the domains of the naive listener and the given outside
functions. -/
abbrev interp : Interp Dom F K := .ofField (domOf K) call

/-- The meaning of the first table: the number one. -/
def stage₀ : (ℕ → ℕ) → K := fun _ ↦ 1
/-- The meaning of the table of `term₁`. -/
def stage₁ := (term₁ : Term Dom F).denote (interp call) size [stage₀]
/-- The meaning of the table of `term₂`. -/
def stage₂ := (term₂ : Term Dom F).denote (interp call) size [stage₀, stage₁ call]
/-- The meaning of the table of the weight. -/
def stage₃ := wt.denote (interp call) size [stage₀, stage₁ call, stage₂ call]
/-- The meaning of the table of `term₄`. -/
def stage₄ := (term₄ : Term Dom F).denote (interp call) size
  [stage₀, stage₁ call, stage₂ call, stage₃ call wt]
/-- The meaning of the table of `term₅`. -/
def stage₅ := (term₅ : Term Dom F).denote (interp call) size
  [stage₀, stage₁ call, stage₂ call, stage₃ call wt, stage₄ call wt]
/-- The meaning of the table of `term₆`. -/
def stage₆ := (term₆ : Term Dom F).denote (interp call) size
  [stage₀, stage₁ call, stage₂ call, stage₃ call wt, stage₄ call wt, stage₅ call wt]
/-- The meaning of the table of `term₇`. -/
def stage₇ := (term₇ : Term Dom F).denote (interp call) size
  [stage₀, stage₁ call, stage₂ call, stage₃ call wt, stage₄ call wt, stage₅ call wt,
    stage₆ call wt]
/-- The meaning of the returned term. -/
def stageRet := (termRet : Term Dom F).denote (interp call) size
  [stage₀, stage₁ call, stage₂ call, stage₃ call wt, stage₄ call wt, stage₅ call wt,
    stage₆ call wt, stage₇ call wt]

omit [IsStrictOrderedRing K] in
theorem term_denote :
    (program wt).term.denote (interp call) size [stage₀] = stageRet call wt := rfl

omit [IsStrictOrderedRing K] in
theorem stage₁_eq (σ) : stage₁ call σ = 1 := by
  show ((1 : ℚ) : K) = 1
  norm_num

omit [IsStrictOrderedRing K] in
theorem stage₂_eq (σ) : stage₂ call σ = 1 / 3 := by
  show stage₀ σ * (stage₁ call σ / ∑ j ∈ Finset.range 3, stage₁ call (Function.update σ 2 j)) = _
  simp [stage₁_eq, stage₀]

variable {call wt} {w : ℕ → ℕ → K} (hw : ∀ σ, stage₃ call wt σ = w (σ 3) (σ 2))
include hw

omit [IsStrictOrderedRing K] in
theorem stage₄_eq (σ) : stage₄ call wt σ = speaker w (σ 3) (σ 2) := by
  show stage₂ call σ * (stage₃ call wt σ /
    ∑ j ∈ Finset.range 4, stage₃ call wt (Function.update σ 3 j)) = _
  simp [Finset.sum_range_succ, stage₂_eq, hw, speaker, Function.update]

omit [IsStrictOrderedRing K] in
theorem stage₅_eq (σ) : stage₅ call wt σ = posterior w (σ 3) (σ 2) := by
  show stage₄ call wt σ / ∑ j ∈ Finset.range 3, stage₄ call wt (Function.update σ 2 j) = _
  simp [Finset.sum_range_succ, stage₄_eq hw, posterior, Function.update]

theorem stage₆_eq (σ) (h : σ 4 < 3) : stage₆ call wt σ = posterior w (σ 0) (σ 4) := by
  show ∑ j ∈ Finset.range 3, (if (j : K) = (σ 4 : K) then 1 else 0) *
    stage₅ call wt (Function.update (fun i ↦ σ ((List.lookup i [(3, 0)]).getD i)) 2 j) = _
  obtain ⟨k, hk⟩ : ∃ k, σ 4 = k := ⟨_, rfl⟩
  rw [hk] at h ⊢
  interval_cases k <;>
    simp [Finset.sum_range_succ, stage₅_eq hw, Function.update, List.lookup]

theorem stage₇_eq (σ) (h : σ 4 < 3) : stage₇ call wt σ = listener w (σ 0) (σ 4) := by
  show stage₀ σ * (stage₆ call wt σ /
    ∑ j ∈ Finset.range 3, stage₆ call wt (Function.update σ 4 j)) = _
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, stage₆_eq hw σ h,
    stage₆_eq hw _ (by simp), stage₆_eq hw _ (by simp), stage₆_eq hw _ (by simp)]
  simp [stage₀, listener, Function.update]

theorem stageRet_eq (σ) (h : σ 1 < 3) : stageRet call wt σ = listener w (σ 0) (σ 1) := by
  show ∑ j ∈ Finset.range 3,
    (if (((Function.update σ 4 j) ((List.lookup 4 [(3, 0)]).getD 4) : ℕ) : K)
      = (Function.update σ 4 j 1 : K) then 1 else 0) * stage₇ call wt (Function.update σ 4 j) = _
  obtain ⟨k, hk⟩ : ∃ k, σ 1 = k := ⟨_, rfl⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    stage₇_eq hw _ (by simp), stage₇_eq hw _ (by simp), stage₇_eq hw _ (by simp), hk]
  rw [hk] at h
  interval_cases k <;> simp [Function.update, List.lookup, hk]

omit [IsStrictOrderedRing K] hw in
theorem size_program : (program wt).size (interp call) = size := by
  funext i
  match i with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | i + 5 => rfl

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] hw in
theorem inRange (a b : ℕ) (ha : a < 4) (hb : b < 3) :
    InRange size (Table.assign [0, 1] [a, b]) := fun i ↦ by
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | 2 | 4 => exact (by decide : 0 < 3)
  | 3 => exact (by decide : 0 < 4)
  | i + 5 => exact Nat.one_pos

theorem get_table (a b : ℕ) (ha : a < 4) (hb : b < 3) :
    ((program wt).term.eval (interp call) size #[.const 1]).get size (Table.assign [0, 1] [a, b]) =
      listener w a b :=
  (Term.get_eval (program wt).term _ _ Env.one _ (inRange a b ha hb)).trans (stageRet_eq hw _ hb)

/-- The array of the program: the entry at an utterance and a referent is the probability that the
listener chooses the referent on hearing the utterance. -/
theorem entries_program : (program wt).entries (interp call) =
    [listener w 0 0, listener w 0 1, listener w 0 2, listener w 1 0, listener w 1 1,
     listener w 1 2, listener w 2 0, listener w 2 1, listener w 2 2,
     listener w 3 0, listener w 3 1, listener w 3 2] := by
  rw [← get_table hw 0 0 (by norm_num) (by norm_num),
    ← get_table hw 0 1 (by norm_num) (by norm_num),
    ← get_table hw 0 2 (by norm_num) (by norm_num),
    ← get_table hw 1 0 (by norm_num) (by norm_num),
    ← get_table hw 1 1 (by norm_num) (by norm_num),
    ← get_table hw 1 2 (by norm_num) (by norm_num),
    ← get_table hw 2 0 (by norm_num) (by norm_num),
    ← get_table hw 2 1 (by norm_num) (by norm_num),
    ← get_table hw 2 2 (by norm_num) (by norm_num),
    ← get_table hw 3 0 (by norm_num) (by norm_num),
    ← get_table hw 3 1 (by norm_num) (by norm_num),
    ← get_table hw 3 2 (by norm_num) (by norm_num),
    Program.entries, Program.table, size_program]
  rfl

omit hw

section Shape

/-- The array of a listener who, on hearing *green*, gives the green square the probability `p`,
and on hearing *round* gives the pink circle the probability `p`. -/
def arrayOf (p : K) : List K := [p, 1 - p, 0, 0, 0, 1, 1, 0, 0, 0, 1 - p, p]

/-- The weight of an utterance for a referent, when the speaker weighs an utterance that describes
the referent by `g` of the probability that a listener with the array `l` gives the referent on
hearing it. -/
def weight (g : K → K) (l : List K) (u r : ℕ) : K := denotesOf (u : K) (r : K) *
  g (Model.lookup [domOf K .U, domOf K .R] l fun i ↦ if i = 0 then (u : K) else r)

theorem getD_find?_range (n u : ℕ) (h : u < n) :
    ((List.range n).find? fun j : ℕ ↦ (j : K) == (u : K)).getD 0 = u := by
  rw [(List.find?_range_eq_some (i := u)).2 ⟨by simp, by simpa using h, fun j hj ↦ by
    simpa using hj.ne⟩]
  rfl

theorem index_utterance (u : ℕ) (h : u < 4) : (domOf K .U).index (u : K) = u :=
  getD_find?_range 4 u h

theorem index_referent (r : ℕ) (h : r < 3) : (domOf K .R).index (r : K) = r :=
  getD_find?_range 3 r h

theorem weight_eq (g : K → K) (l : List K) (u r : ℕ) (hu : u < 4) (hr : r < 3) :
    weight g l u r = denotesOf (u : K) (r : K) * g (l.getD (u * 3 + r) 0) := by
  show _ * g (l.getD
    ((0 * 4 + (domOf K .U).index (u : K)) * 3 + (domOf K .R).index (r : K)) 0) = _
  rw [index_utterance u hu, index_referent r hr, Nat.zero_mul, Nat.zero_add]

/-- **The step from one depth to the next.** Over a listener who gives the green square the
probability `p` on hearing *green*, a speaker who weighs an utterance by `g` of the listener's
probability makes the next listener give it `2 * g p / (3 * g p + g 1)`. -/
theorem listener_weight (g : K → K) (p : K) (ha : 0 < g p) (hb : 0 < g 1) (hd : 0 < g (1 - p)) :
    [listener (weight g (arrayOf p)) 0 0, listener (weight g (arrayOf p)) 0 1,
     listener (weight g (arrayOf p)) 0 2, listener (weight g (arrayOf p)) 1 0,
     listener (weight g (arrayOf p)) 1 1, listener (weight g (arrayOf p)) 1 2,
     listener (weight g (arrayOf p)) 2 0, listener (weight g (arrayOf p)) 2 1,
     listener (weight g (arrayOf p)) 2 2, listener (weight g (arrayOf p)) 3 0,
     listener (weight g (arrayOf p)) 3 1, listener (weight g (arrayOf p)) 3 2] =
    arrayOf (2 * g p / (3 * g p + g 1)) := by
  simp only [listener, posterior, speaker,
    weight_eq g _ _ _ (by norm_num : (0 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (0 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (0 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (1 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (1 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (1 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (2 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (2 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (2 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (3 : ℕ) < 4) (by norm_num : (0 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (3 : ℕ) < 4) (by norm_num : (1 : ℕ) < 3),
    weight_eq g _ _ _ (by norm_num : (3 : ℕ) < 4) (by norm_num : (2 : ℕ) < 3), arrayOf, denotesOf]
  norm_num
  generalize g p = a at ha ⊢
  generalize g 1 = b at hb ⊢
  generalize g (1 - p) = d at hd ⊢
  have e : d / (d + d) = 1 / 2 := by field_simp; ring
  rw [e]
  and_intros
  all_goals first
    | (apply ne_of_gt; positivity)
    | (field_simp; ring)

end Shape

end Memo.Listener
