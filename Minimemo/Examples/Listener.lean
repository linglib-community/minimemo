/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Examples.NaiveListener
public import Minimemo.Theory.Denote
public import Mathlib.Algebra.Order.Field.Basic
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

variable {F : ℕ → Type}

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
  .rename [(3, 0)] (Term.expect 5 [2] (.app (.inl .eq) [.rename [] (.val 2 .R), .val 4 .R]))
/-- The listener chooses a referent. -/
def term₇ : Term Dom F := Term.chooses 0 [4] (.ref 6)
/-- The probability that the listener chooses the referent of the second axis. -/
def termRet : Term Dom F :=
  Term.expect 7 [4] (.app (.inl .eq) [.rename [(3, 0)] (.val 4 .R), .val 1 .R])

/-- The program of the model, with `wt` the term for the weight of the utterance. -/
def program (wt : Term Dom F) : Program Dom F :=
  ⟨[.U, .R, .R, .U, .R], [term₁, term₂, wt, term₄, term₅, term₆, term₇], termRet, [0, 1]⟩

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The sizes of the choices of the model: the axes `0` and `1`, the referent `2` and the
utterance `3` of the speaker, and the referent `4` that the listener chooses. -/
def size (dom : Dom → Domain K) (i : ℕ) : ℕ :=
  ([(dom .U).size, (dom .R).size, (dom .R).size, (dom .U).size, (dom .R).size] : List ℕ).getD i 1

section Weight

variable (nU nR : ℕ) (w : ℕ → ℕ → K)

/-- The probability that the listener thinks the speaker chooses the referent at position `r` and
then the utterance at position `u`, among `nU` utterances and `nR` referents. -/
def speaker (u r : ℕ) : K := 1 / nR * (w u r / ∑ u' ∈ Finset.range nU, w u' r)
/-- The probability that the listener gives to the referent at position `r` on hearing the
utterance at position `u`. -/
def posterior (u r : ℕ) : K :=
  speaker nU nR w u r / ∑ r' ∈ Finset.range nR, speaker nU nR w u r'
/-- The probability that the listener chooses the referent at position `r` on hearing the
utterance at position `u`. -/
def listener (u r : ℕ) : K :=
  posterior nU nR w u r / ∑ r' ∈ Finset.range nR, posterior nU nR w u r'

end Weight

variable (dom : Dom → Domain K) (call : {k : ℕ} → F k → (Fin k → K) → K) (wt : Term Dom F)

/-- The interpretation of the model: the given domains and outside functions. -/
abbrev interp : Interp Dom F K := .ofField dom call

/-- The meaning of the first table: the number one. -/
def stage₀ : (ℕ → ℕ) → K := fun _ ↦ 1
/-- The meaning of the table of `term₁`. -/
def stage₁ := (term₁ : Term Dom F).denote (interp dom call) (size dom) [stage₀]
/-- The meaning of the table of `term₂`. -/
def stage₂ := (term₂ : Term Dom F).denote (interp dom call) (size dom) [stage₀, stage₁ dom call]
/-- The meaning of the table of the weight. -/
def stage₃ := wt.denote (interp dom call) (size dom) [stage₀, stage₁ dom call, stage₂ dom call]
/-- The meaning of the table of `term₄`. -/
def stage₄ := (term₄ : Term Dom F).denote (interp dom call) (size dom)
  [stage₀, stage₁ dom call, stage₂ dom call, stage₃ dom call wt]
/-- The meaning of the table of `term₅`. -/
def stage₅ := (term₅ : Term Dom F).denote (interp dom call) (size dom)
  [stage₀, stage₁ dom call, stage₂ dom call, stage₃ dom call wt, stage₄ dom call wt]
/-- The meaning of the table of `term₆`. -/
def stage₆ := (term₆ : Term Dom F).denote (interp dom call) (size dom)
  [stage₀, stage₁ dom call, stage₂ dom call, stage₃ dom call wt, stage₄ dom call wt,
    stage₅ dom call wt]
/-- The meaning of the table of `term₇`. -/
def stage₇ := (term₇ : Term Dom F).denote (interp dom call) (size dom)
  [stage₀, stage₁ dom call, stage₂ dom call, stage₃ dom call wt, stage₄ dom call wt,
    stage₅ dom call wt, stage₆ dom call wt]
/-- The meaning of the returned term. -/
def stageRet := (termRet : Term Dom F).denote (interp dom call) (size dom)
  [stage₀, stage₁ dom call, stage₂ dom call, stage₃ dom call wt, stage₄ dom call wt,
    stage₅ dom call wt, stage₆ dom call wt, stage₇ dom call wt]

omit [IsStrictOrderedRing K] in
theorem term_denote :
    (program wt).term.denote (interp dom call) (size dom) [stage₀] = stageRet dom call wt := rfl

omit [IsStrictOrderedRing K] in
theorem stage₁_eq (σ) : stage₁ dom call σ = 1 := by
  show ((1 : ℚ) : K) = 1
  norm_num

omit [IsStrictOrderedRing K] in
theorem stage₂_eq (σ) : stage₂ dom call σ = 1 / (dom .R).size := by
  show stage₀ σ * (stage₁ dom call σ /
    ∑ j ∈ Finset.range (dom .R).size, stage₁ dom call (Function.update σ 2 j)) = _
  simp [stage₁_eq, stage₀]

-- the choice that the listener observes is read at the first axis
omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem lookup_link (i : ℕ) :
    ((List.filter (fun l : ℕ × ℕ ↦ size dom l.1 == size dom l.2) [(3, 0)]).lookup i).getD i =
      if i = 3 then 0 else i := by
  have h : (size dom 3 == size dom 0) = true := by simp [size]
  by_cases hi : i = 3
  · simp [List.filter, h, hi]
  · have : (i == 3) = false := by simpa using hi
    simp [List.filter, h, hi, this]

variable {dom call wt} {w : ℕ → ℕ → K} (hw : ∀ σ, stage₃ dom call wt σ = w (σ 3) (σ 2))
include hw

omit [IsStrictOrderedRing K] in
theorem stage₄_eq (σ) :
    stage₄ dom call wt σ = speaker (dom .U).size (dom .R).size w (σ 3) (σ 2) := by
  show stage₂ dom call σ * (stage₃ dom call wt σ /
    ∑ j ∈ Finset.range (dom .U).size, stage₃ dom call wt (Function.update σ 3 j)) = _
  simp [stage₂_eq, hw, speaker, Function.update]

omit [IsStrictOrderedRing K] in
theorem stage₅_eq (σ) :
    stage₅ dom call wt σ = posterior (dom .U).size (dom .R).size w (σ 3) (σ 2) := by
  show stage₄ dom call wt σ /
    ∑ j ∈ Finset.range (dom .R).size, stage₄ dom call wt (Function.update σ 2 j) = _
  simp [stage₄_eq hw, posterior, Function.update]

variable (hR : ∀ j, (dom .R).val j = (j : K))
include hR

theorem stage₆_eq (σ) (h : σ 4 < (dom .R).size) :
    stage₆ dom call wt σ = posterior (dom .U).size (dom .R).size w (σ 0) (σ 4) := by
  show ∑ j ∈ Finset.range (dom .R).size,
    (if (dom .R).val (Function.update (fun i ↦ σ (((List.filter (fun l : ℕ × ℕ ↦
        size dom l.1 == size dom l.2) [(3, 0)]).lookup i).getD i)) 2 j 2) =
      (dom .R).val (Function.update (fun i ↦ σ (((List.filter (fun l : ℕ × ℕ ↦
        size dom l.1 == size dom l.2) [(3, 0)]).lookup i).getD i)) 2 j 4) then 1 else 0) *
    stage₅ dom call wt (Function.update (fun i ↦ σ (((List.filter (fun l : ℕ × ℕ ↦
        size dom l.1 == size dom l.2) [(3, 0)]).lookup i).getD i)) 2 j) = _
  simp only [lookup_link, stage₅_eq hw, hR, Function.update, Nat.cast_inj]
  simp [Finset.sum_ite_eq', h, ite_mul]

theorem stage₇_eq (σ) (h : σ 4 < (dom .R).size) :
    stage₇ dom call wt σ = listener (dom .U).size (dom .R).size w (σ 0) (σ 4) := by
  show stage₀ σ * (stage₆ dom call wt σ /
    ∑ j ∈ Finset.range (dom .R).size, stage₆ dom call wt (Function.update σ 4 j)) = _
  rw [stage₆_eq hw hR σ h, Finset.sum_congr rfl fun j hj ↦
    stage₆_eq hw hR (Function.update σ 4 j) (by simpa using Finset.mem_range.1 hj)]
  simp [stage₀, listener, Function.update]

theorem stageRet_eq (σ) (h : σ 1 < (dom .R).size) :
    stageRet dom call wt σ = listener (dom .U).size (dom .R).size w (σ 0) (σ 1) := by
  show ∑ j ∈ Finset.range (dom .R).size,
    (if (dom .R).val ((fun i ↦ Function.update σ 4 j (((List.filter (fun l : ℕ × ℕ ↦
        size dom l.1 == size dom l.2) [(3, 0)]).lookup i).getD i)) 4) =
      (dom .R).val (Function.update σ 4 j 1) then 1 else 0) *
    stage₇ dom call wt (Function.update σ 4 j) = _
  rw [Finset.sum_congr rfl fun j hj ↦ by
    rw [stage₇_eq hw hR (Function.update σ 4 j) (by simpa using Finset.mem_range.1 hj)]]
  simp only [lookup_link, hR, Function.update, Nat.cast_inj]
  simp [Finset.sum_ite_eq', h, ite_mul]

omit [IsStrictOrderedRing K] hw hR in
theorem size_program : (program wt).size (interp dom call) = size dom := by
  funext i
  match i with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | i + 5 => rfl

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] hw hR in
theorem inRange (a b : ℕ) (ha : a < (dom .U).size) (hb : b < (dom .R).size) :
    InRange (size dom) (Table.assign [0, 1] [a, b]) := fun i ↦ by
  match i with
  | 0 => exact ha
  | 1 => exact hb
  | 2 | 4 => exact Nat.zero_lt_of_lt hb
  | 3 => exact Nat.zero_lt_of_lt ha
  | i + 5 => exact Nat.one_pos

/-- The table of the program has, at an utterance and a referent, the probability that the
listener chooses the referent on hearing the utterance. -/
theorem get_table (a b : ℕ) (ha : a < (dom .U).size) (hb : b < (dom .R).size) :
    ((program wt).term.eval (interp dom call) (size dom) #[.const 1]).get (size dom)
      (Table.assign [0, 1] [a, b]) = listener (dom .U).size (dom .R).size w a b :=
  (Term.get_eval (program wt).term _ _ Env.one _ (inRange a b ha hb)).trans
    (stageRet_eq hw hR _ hb)

omit hw hR

section Paper

/-! ### The game of four utterances and three referents -/

variable {call : {k : ℕ} → F k → (Fin k → K) → K} {wt : Term Dom F} {w : ℕ → ℕ → K}

/-- The array of the program in the game of four utterances and three referents. -/
theorem entries_program (hw : ∀ σ, stage₃ (domOf K) call wt σ = w (σ 3) (σ 2)) :
    (program wt).entries (interp (domOf K) call) =
    [listener 4 3 w 0 0, listener 4 3 w 0 1, listener 4 3 w 0 2, listener 4 3 w 1 0,
     listener 4 3 w 1 1, listener 4 3 w 1 2, listener 4 3 w 2 0, listener 4 3 w 2 1,
     listener 4 3 w 2 2, listener 4 3 w 3 0, listener 4 3 w 3 1, listener 4 3 w 3 2] := by
  have g (a b : ℕ) (ha : a < 4) (hb : b < 3) :
      ((program wt).term.eval (interp (domOf K) call) (size (domOf K)) #[.const 1]).get
        (size (domOf K)) (Table.assign [0, 1] [a, b]) = listener 4 3 w a b :=
    get_table hw (fun _ ↦ rfl) a b ha hb
  rw [← g 0 0 (by norm_num) (by norm_num), ← g 0 1 (by norm_num) (by norm_num),
    ← g 0 2 (by norm_num) (by norm_num), ← g 1 0 (by norm_num) (by norm_num),
    ← g 1 1 (by norm_num) (by norm_num), ← g 1 2 (by norm_num) (by norm_num),
    ← g 2 0 (by norm_num) (by norm_num), ← g 2 1 (by norm_num) (by norm_num),
    ← g 2 2 (by norm_num) (by norm_num), ← g 3 0 (by norm_num) (by norm_num),
    ← g 3 1 (by norm_num) (by norm_num), ← g 3 2 (by norm_num) (by norm_num),
    Program.entries, Program.table, size_program]
  rfl

end Paper

section Shape

/-- The array of a listener who, on hearing *green*, gives the green square the probability `p`,
and on hearing *round* gives the pink circle the probability `p`. -/
def arrayOf (p : K) : List K := [p, 1 - p, 0, 0, 0, 1, 1, 0, 0, 0, 1 - p, p]

/-- The weight of an utterance for a referent, when the speaker weighs an utterance that describes
the referent by `g` of the probability that a listener with the array `l` gives the referent on
hearing it. -/
def weight (g : K → K) (l : List K) (u r : ℕ) : K := denotesOf (u : K) (r : K) *
  g (Model.lookup [domOf K .U, domOf K .R] l fun i ↦ if h : i < 2 then ![(u : K), r] ⟨i, h⟩ else 0)

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
    [listener 4 3 (weight g (arrayOf p)) 0 0, listener 4 3 (weight g (arrayOf p)) 0 1,
     listener 4 3 (weight g (arrayOf p)) 0 2, listener 4 3 (weight g (arrayOf p)) 1 0,
     listener 4 3 (weight g (arrayOf p)) 1 1, listener 4 3 (weight g (arrayOf p)) 1 2,
     listener 4 3 (weight g (arrayOf p)) 2 0, listener 4 3 (weight g (arrayOf p)) 2 1,
     listener 4 3 (weight g (arrayOf p)) 2 2, listener 4 3 (weight g (arrayOf p)) 3 0,
     listener 4 3 (weight g (arrayOf p)) 3 1, listener 4 3 (weight g (arrayOf p)) 3 2] =
    arrayOf (2 * g p / (3 * g p + g 1)) := by
  simp only [listener, posterior, speaker, Finset.sum_range_succ, Finset.sum_range_zero,
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
