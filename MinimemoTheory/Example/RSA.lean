/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Example.Listener
public import MinimemoTheory.Kernel
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Algebra.Order.Field
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
* `Memo.RSA.family`: the listeners at every depth, as a family of models.
* `Memo.RSA.level β t`: the array of the listener at depth `t`, with real numbers.
* `Memo.RSA.prob β t`: the probability that the recursion gives the green square at depth `t`.

## Main results

* `Memo.RSA.level_eq`: the array of the listener at every depth.
* `Memo.RSA.kernel_family`: the kernel of the listener at every depth.
* `Memo.RSA.greenSquare_eq`: on hearing *green*, the listener at depth `t` gives the green square
  the probability `prob β t`.
* `Memo.RSA.prob_succ`: the step `p ↦ 2 / (3 + exp (β * (1 - p)))`.
* `Memo.RSA.prob_zero_left`: when `β` is zero, the probability is one half at every depth.
* `Memo.RSA.prob_le_half`: when `β` is not negative, the green square is at most as likely as the
  green circle at every depth.
* `Memo.RSA.tendsto_prob`: when `β` is not negative, the probability falls with the depth to
  `limit β`.
* `Memo.RSA.step_limit`, `Memo.RSA.le_limit`: the limit is the greatest probability `p` with
  `p = 2 / (3 + exp (β * (1 - p)))`.
* `Memo.RSA.limit_anti`, `Memo.RSA.tendsto_limit`: the limit falls as `β` grows, from one half at
  zero, and tends to zero.

## Implementation notes

The real numbers are not computed with: the results are proved on the meaning of the program, in
which the array of the listener below is a variable. The same model is run in floating point,
against memo, by the tests in `tests/test_examples.py`.

The parameter `β` is an outside function of no arguments, whose value the interpretation gives.
So the model is one program for every `β`, and `β` is any real number.

## TODO

For `β` not negative, the equation `p = 2 / (3 + exp (β * (1 - p)))` should have one solution
only, so that the limit is the solution. Here the limit is shown to be the greatest solution.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

namespace Memo.RSA

open NaiveListener (Agent Name Dom domOf denotesOf)
open Listener (arrayOf)

/-- The outside functions of the model: the denotation, the exponential, and the parameter `β`. -/
inductive Fn : ℕ → Type
  | denotes : Fn 2
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
It has one reference, to the listener below. -/
def model (t : ℕ) : Model Agent Name Dom (Refs Unit Fn) where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U
        (.prim .mul ![.fn .denotes ![.choice .uSaid, .choice .rTrue],
          if t = 0 then .lit 1
          else .fn .exp ![.prim .mul ![.fn .beta ![],
            .ref () ![.choice .uSaid, .choice .rTrue]]]])) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.prim .eq ![.query .speaker (.choice .rTrue), .choice .rPick]))
  ret := .expect (.prim .eq ![.query .listener (.choice .rPick), .choice .r])

/-- The listeners at every depth: the reference of the listener at depth `t` names the listener at
depth `t - 1`. -/
def family : Family Agent Name Dom Fn ℕ Unit where
  model := model
  target t _ := t - 1

/-- The meaning of the outside functions in the real numbers, for the parameter `β`. -/
noncomputable def callOf (β : ℝ) : {k : ℕ} → Fn k → (Fin k → ℝ) → ℝ
  | _, .denotes, v => denotesOf (v 0) (v 1)
  | _, .exp, v => Real.exp (v 0)
  | _, .beta, _ => β

/-- The array of the listener at depth `t`, with real numbers: one entry for each utterance and
referent, in row-major order. -/
noncomputable def level (β : ℝ) (t : ℕ) : List ℝ :=
  family.entries .ofField (domOf ℝ) (callOf β) (t + 1) t

/-- The probability that the recursion gives the green square on hearing *green*, at depth `t`. -/
noncomputable def prob (β : ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | t + 1 => 2 * Real.exp (β * prob β t) / (3 * Real.exp (β * prob β t) + Real.exp (β * 1))

section Step

/-- The term for the weight of the utterance at depth zero: the denotation. -/
def weightTerm₀ : Term Dom (Refs Unit Fn) :=
  .rename [] (.app (.inl .mul) [.app (.inr (.inr .denotes)) [.val 3 .U, .val 2 .R], .lit 1])

/-- The term for the weight of the utterance at a depth above zero: the denotation times the
exponential of `β` times the probability that the listener below gives the referent. -/
def weightTerm : Term Dom (Refs Unit Fn) :=
  .rename [] (.app (.inl .mul) [.app (.inr (.inr .denotes)) [.val 3 .U, .val 2 .R],
    .app (.inr (.inr .exp)) [.app (.inl .mul) [.app (.inr (.inr .beta)) [],
      .app (k := 2) (.inr (.inl ())) [.val 3 .U, .val 2 .R]]]])

theorem program_zero : Model.program (model 0) = .ok (Listener.program weightTerm₀) :=
  rfl

theorem program_one : Model.program (model 1) = .ok (Listener.program weightTerm) :=
  rfl

theorem model_succ (t : ℕ) : model (t + 1) = model 1 := by
  simp [model]

/-- The listener at depth zero gives the green square the probability one half on hearing
*green*. -/
theorem level_zero (β : ℝ) : level β 0 = arrayOf (1 / 2) := by
  show (Model.entries _ (model 0)).getD [] = _
  rw [Model.entries, program_zero]
  show (Listener.program weightTerm₀).entries _ = _
  rw [Listener.entries_program (w := Listener.weight (fun _ ↦ 1) (arrayOf 0)) fun σ ↦ by
      show _ * ((1 : ℚ) : ℝ) = _ * 1
      rw [Rat.cast_one]
      rfl,
    Listener.listener_weight (fun _ ↦ 1) 0 one_pos one_pos one_pos]
  norm_num

/-- **The step from one depth to the next**: over a listener with the array `arrayOf p`, the
listener at the next depth has the array of the probability
`2 * exp (β * p) / (3 * exp (β * p) + exp β)`. -/
theorem entries_model (β : ℝ) (below : ℕ → List ℝ) (t : ℕ) (p : ℝ) (h : below t = arrayOf p) :
    Model.entries (.ofField (domOf ℝ) (family.call (domOf ℝ) (callOf β) below (t + 1)))
      (model (t + 1)) =
      some (arrayOf (2 * Real.exp (β * p) / (3 * Real.exp (β * p) + Real.exp (β * 1)))) := by
  rw [model_succ, Model.entries, program_one]
  show some ((Listener.program weightTerm).entries _) = _
  rw [Listener.entries_program (w := Listener.weight (fun x ↦ Real.exp (β * x)) (below t))
      fun σ ↦ rfl, h,
    Listener.listener_weight (fun x ↦ Real.exp (β * x)) p (Real.exp_pos _) (Real.exp_pos _)
      (Real.exp_pos _)]

theorem refs_one : (model 1).refs = [()] := by decide

/-- The array at a depth above zero is the array of the model over the array one depth below. -/
theorem level_succ (β : ℝ) (t : ℕ) :
    level β (t + 1) = (Model.entries (.ofField (domOf ℝ)
      (family.call (domOf ℝ) (callOf β) (fun q ↦ if q = t then level β t else []) (t + 1)))
      (model (t + 1))).getD [] := by
  have hb : (fun q ↦ (((model (t + 1)).refs.map fun r ↦ (family.target (t + 1) r,
      family.entries .ofField (domOf ℝ) (callOf β) (t + 1) (family.target (t + 1) r))).lookup
        q).getD []) = fun q ↦ if q = t then level β t else [] := by
    funext q
    rw [model_succ, refs_one]
    have hq : (q == t) = decide (q = t) := rfl
    by_cases h : q = t <;> simp [List.lookup, family, level, hq, h]
  rw [← hb]
  rfl

end Step

/-- The array of the listener at every depth. -/
theorem level_eq (β : ℝ) (t : ℕ) : level β t = arrayOf (prob β t) := by
  induction t with
  | zero => exact level_zero β
  | succ t ih =>
    rw [level_succ, entries_model β _ t _ (by simpa using ih), Option.getD_some, prob]

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

/-- **The kernel of the listener** at depth `t`: on hearing the utterance at a position, the
referent at a position has the probability in the array of `prob β t`. -/
theorem kernel_family (β : ℝ) (t i j : ℕ) :
    family.kernel (domOf ℝ) (callOf β) (t + 1) t i {j} = ENNReal.ofReal
      ((([[prob β t, 1 - prob β t, 0], [0, 0, 1], [1, 0, 0], [0, 1 - prob β t, prob β t]] :
        List (List ℝ)).getD i []).getD j 0) := by
  rw [Family.kernel, rowsKernel_apply_singleton]
  have h : family.entries .ofField (domOf ℝ) (callOf β) (t + 1) t = arrayOf (prob β t) :=
    level_eq β t
  have hw : (((family.model t).axes.getLast?.map fun a ↦ (domOf ℝ a.2).size).getD 1) = 3 := rfl
  have hc : chunks 3 (arrayOf (prob β t)) =
      [[prob β t, 1 - prob β t, 0], [0, 0, 1], [1, 0, 0], [0, 1 - prob β t, prob β t]] := by
    simp [chunks, arrayOf, List.range_succ]
  rw [h, hw, hc]

section Limit

/-! ### The limit of the recursion -/

/-- One more depth of reasoning, on the probability of the green square. -/
noncomputable def step (β p : ℝ) : ℝ := 2 / (3 + Real.exp (β * (1 - p)))

theorem prob_succ' (β : ℝ) (t : ℕ) : prob β (t + 1) = step β (prob β t) := prob_succ β t

theorem step_pos (β p : ℝ) : 0 < step β p := by
  unfold step
  positivity

/-- A listener who finds the green square more likely is followed by one who does. -/
theorem step_mono {β : ℝ} (hβ : 0 ≤ β) : Monotone (step β) := fun p q h ↦ by
  have he : Real.exp (β * (1 - q)) ≤ Real.exp (β * (1 - p)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hβ)
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-- A more rational speaker makes the next listener find the green square less likely. -/
theorem step_anti_left {β γ p : ℝ} (h : β ≤ γ) (hp : p ≤ 1) : step γ p ≤ step β p := by
  have he : Real.exp (β * (1 - p)) ≤ Real.exp (γ * (1 - p)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (by linarith))
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

theorem continuous_step (β : ℝ) : Continuous (step β) := by
  unfold step
  exact continuous_const.div (by fun_prop) fun p ↦ by positivity

/-- A probability that one more depth of reasoning leaves unchanged is at most one half. -/
theorem le_half_of_step_eq {β p : ℝ} (hβ : 0 ≤ β) (h : step β p = p) : p ≤ 1 / 2 := by
  have h3 : p < 1 := by
    rw [← h, step, div_lt_one (by positivity)]
    linarith [Real.exp_pos (β * (1 - p))]
  have h1 : 1 ≤ Real.exp (β * (1 - p)) := Real.one_le_exp (mul_nonneg hβ (by linarith))
  rw [← h, step, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- When `β` is not negative, each further depth of reasoning makes the green square at most as
likely on hearing *green*. -/
theorem prob_antitone {β : ℝ} (hβ : 0 ≤ β) : Antitone (prob β) := by
  refine antitone_nat_of_succ_le fun t ↦ ?_
  induction t with
  | zero => exact (prob_le_half hβ 1).2
  | succ t ih =>
    rw [prob_succ' β (t + 1)]
    exact (step_mono hβ ih).trans_eq (prob_succ' β t).symm

/-- A more rational speaker makes the listener find the green square at most as likely, at every
depth. -/
theorem prob_anti_left {β γ : ℝ} (hβ : 0 ≤ β) (h : β ≤ γ) (t : ℕ) : prob γ t ≤ prob β t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    rw [prob_succ', prob_succ']
    exact (step_mono (hβ.trans h) ih).trans
      (step_anti_left h (by linarith [(prob_le_half hβ t).2]))

/-- The probability of the green square on hearing *green*, for a listener who reasons to every
depth. -/
noncomputable def limit (β : ℝ) : ℝ := ⨅ t, prob β t

theorem bddBelow_prob {β : ℝ} (hβ : 0 ≤ β) : BddBelow (Set.range (prob β)) :=
  ⟨0, by rintro _ ⟨t, rfl⟩; exact (prob_le_half hβ t).1.le⟩

/-- As the depth of reasoning grows, the probability of the green square on hearing *green* tends
to `limit β`. -/
theorem tendsto_prob {β : ℝ} (hβ : 0 ≤ β) :
    Filter.Tendsto (prob β) Filter.atTop (nhds (limit β)) :=
  tendsto_atTop_ciInf (prob_antitone hβ) (bddBelow_prob hβ)

/-- One more depth of reasoning leaves the limit unchanged:
`limit β = 2 / (3 + exp (β * (1 - limit β)))`. -/
theorem step_limit {β : ℝ} (hβ : 0 ≤ β) : step β (limit β) = limit β := by
  have h1 : Filter.Tendsto (fun t ↦ prob β (t + 1)) Filter.atTop (nhds (limit β)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 (tendsto_prob hβ)
  have h2 : Filter.Tendsto (fun t ↦ prob β (t + 1)) Filter.atTop (nhds (step β (limit β))) := by
    simp_rw [prob_succ']
    exact ((continuous_step β).tendsto _).comp (tendsto_prob hβ)
  exact tendsto_nhds_unique h2 h1

/-- The limit is a probability, and at most one half. -/
theorem limit_mem {β : ℝ} (hβ : 0 ≤ β) : 0 < limit β ∧ limit β ≤ 1 / 2 :=
  ⟨by rw [← step_limit hβ]; exact step_pos _ _, ciInf_le (bddBelow_prob hβ) 0⟩

/-- The limit is the greatest probability that one more depth of reasoning leaves unchanged. -/
theorem le_limit {β p : ℝ} (hβ : 0 ≤ β) (h : step β p = p) : p ≤ limit β := by
  refine le_ciInf fun t ↦ ?_
  induction t with
  | zero => exact le_half_of_step_eq hβ h
  | succ t ih =>
    rw [prob_succ', ← h]
    exact step_mono hβ ih

/-- When `β` is zero the limit is one half. -/
theorem limit_zero : limit 0 = 1 / 2 := by
  simp [limit, prob_zero_left]

/-- A more rational speaker makes the green square at most as likely in the limit. -/
theorem limit_anti {β γ : ℝ} (hβ : 0 ≤ β) (h : β ≤ γ) : limit γ ≤ limit β :=
  le_of_tendsto_of_tendsto' (tendsto_prob (hβ.trans h)) (tendsto_prob hβ) (prob_anti_left hβ h)

/-- The limit is at most the probability at depth one. -/
theorem limit_le {β : ℝ} (hβ : 0 ≤ β) : limit β ≤ 2 / (3 + Real.exp (β / 2)) := by
  refine (ciInf_le (bddBelow_prob hβ) 1).trans (le_of_eq ?_)
  rw [prob_succ, prob]
  ring_nf

/-- As the speaker grows more rational, the green square becomes impossible in the limit: on
hearing *green*, the listener is sure of the green circle. -/
theorem tendsto_limit : Filter.Tendsto limit Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun β : ℝ ↦ 2 / (3 + Real.exp (β / 2))) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (Filter.tendsto_atTop_add_const_left _ _
      (Real.tendsto_exp_atTop.comp (Filter.tendsto_id.atTop_div_const (by norm_num))))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 0] with β hβ using (limit_mem hβ).1.le
  · filter_upwards [Filter.eventually_ge_atTop 0] with β hβ using limit_le hβ

end Limit

end Memo.RSA
