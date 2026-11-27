/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Theory.Belief.Basic
public import Minimemo.Theory.FiniteMeasure
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Beliefs as measures

This file gives a belief its measures and proves that the statements of memo act on them as the
operations of probability theory.

A belief with nonnegative real numbers gives, at every assignment, a measure on the values of the
choices that the agent is uncertain of: the mass of a point is the number of the factor there. The
measure depends on the assignment only through the choices that the agent is certain of.

## Main definitions

* `Memo.Belief.measure b σ`: the measure of the belief `b` at the assignment `σ`, on the
  values of the uncertain choices.
* `Memo.Belief.choice i w`: the belief in which only the choice `i` is uncertain, with the
  weight `w` divided by its sum over `i`.

## Main results

* `Memo.Belief.isNormalized_iff`: a belief is normalized if and only if each of its measures
  is a probability measure or zero.
* `Memo.Belief.lintegral_measure`: the expectation of a factor is its integral.
* `Memo.Belief.measure_observes`: the measure after an observation is the measure
  conditioned on the observed value, with the observed choice forgotten.
* `Memo.Belief.measure_chooses`: the measure after a choice is the joint measure of the
  measure before it and the kernel of the choice.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Memo.Belief

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
  (b : Belief X ℝ≥0) (σ : ∀ i, X i)

/-- The **measure of a belief** at an assignment, on the values of the uncertain choices: the mass
of a point is the number of the factor at the assignment with those values. -/
noncomputable def measure : Measure (∀ j : b.uncertain, X j) :=
  toMeasure fun τ ↦ b.weight (Function.updateFinset σ b.uncertain τ)

instance : IsFiniteMeasure (b.measure σ) := inferInstanceAs (IsFiniteMeasure (toMeasure _))

omit [∀ i, Fintype (X i)] in
@[simp] theorem measure_apply_singleton (τ : ∀ j : b.uncertain, X j) :
    b.measure σ {τ} = b.weight (Function.updateFinset σ b.uncertain τ) :=
  toMeasure_apply_singleton _ _

omit [∀ i, Fintype (X i)] [∀ i, MeasurableSingletonClass (X i)] in
/-- Beliefs with the same uncertain choices and equal factors have the same measure. -/
theorem measure_congr {u : Finset ι} {f g : Factor X ℝ≥0} (h : f = g) (σ : ∀ i, X i) :
    (Belief.mk u f).measure σ = (Belief.mk u g).measure σ := by
  subst h
  rfl

theorem measure_univ : b.measure σ Set.univ = (b.weight.sumOver b.uncertain σ : ℝ≥0) := by
  rw [measure, toMeasure_univ, Factor.sumOver, ENNReal.ofNNReal_finsetSum]

/-- A belief is normalized if and only if each of its measures is a probability measure or
zero. -/
theorem isNormalized_iff :
    b.IsNormalized ↔ ∀ σ, IsZeroOrProbabilityMeasure (b.measure σ) := by
  refine forall_congr' fun σ ↦ ?_
  rw [isZeroOrProbabilityMeasure_iff, measure_univ, ENNReal.coe_eq_zero, ENNReal.coe_eq_one,
    or_comm]

/-- The expectation of a factor in a belief is its integral against the measure of the belief. -/
theorem lintegral_measure (e : Factor X ℝ≥0) :
    ∫⁻ τ, e (Function.updateFinset σ b.uncertain τ) ∂b.measure σ = (b.expect e σ : ℝ≥0) := by
  rw [measure, lintegral_toMeasure, expect, Factor.sumOver, ENNReal.ofNNReal_finsetSum]
  simp only [Pi.mul_apply, ENNReal.coe_mul]

/-- The measure after an observation is the measure before it conditioned on the event that the
observed choice has the value of the assignment, with the observed choice forgotten. -/
theorem measure_observes {i : ι} (hi : i ∈ b.uncertain) :
    (b.observes i).measure σ =
      ((b.measure σ)[|{τ | τ ⟨i, hi⟩ = σ i}]).map
        (Finset.restrict₂ (Finset.erase_subset i b.uncertain)) := by
  classical
  let r : (∀ j : b.uncertain, X j) → ∀ j : b.uncertain.erase i, X j :=
    Finset.restrict₂ (Finset.erase_subset i b.uncertain)
  let ext : (∀ j : b.uncertain.erase i, X j) → ∀ j : b.uncertain, X j := fun ρ j ↦
    if h : (j : ι) = i then σ j else ρ ⟨j, Finset.mem_erase.2 ⟨h, j.2⟩⟩
  have hext (ρ) : Function.updateFinset σ b.uncertain (ext ρ) =
      Function.updateFinset σ (b.uncertain.erase i) ρ := by
    funext k
    by_cases hk : k ∈ b.uncertain <;> by_cases hki : k = i <;>
      simp [Function.updateFinset, ext, hk, hki, Finset.mem_erase]
  have hr (ρ) : r (ext ρ) = ρ := by
    funext j
    simp [r, ext, Finset.restrict₂, (Finset.mem_erase.1 j.2).1]
  have hA (τ : ∀ j : b.uncertain, X j) (hτ : τ ⟨i, hi⟩ = σ i) : ext (r τ) = τ := by
    funext j
    by_cases h : (j : ι) = i
    · obtain ⟨j, hj⟩ := j
      subst h
      simp [ext, hτ]
    · simp [ext, r, Finset.restrict₂, h]
  have hmass : b.measure σ {τ | τ ⟨i, hi⟩ = σ i} =
      (b.weight.sumOver (b.uncertain.erase i) σ : ℝ≥0) := by
    rw [measure, toMeasure_apply, Factor.sumOver, ENNReal.ofNNReal_finsetSum]
    refine Finset.sum_nbij' r ext (by simp) (fun ρ _ ↦ ?_) (fun τ hτ ↦ hA τ (by simpa using hτ))
      (fun ρ _ ↦ hr ρ) fun τ hτ ↦ ?_
    · simp [ext]
    · rw [← hext, hA τ (by simpa using hτ)]
  refine Measure.ext_of_singleton (α := ∀ j : b.uncertain.erase i, X j) fun ρ ↦ ?_
  have hset : {τ : ∀ j : b.uncertain, X j | τ ⟨i, hi⟩ = σ i} ∩ r ⁻¹' {ρ} = {ext ρ} := by
    ext τ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun ⟨h₁, h₂⟩ ↦ by rw [← h₂, hA τ h₁], fun h ↦ ?_⟩
    subst h
    exact ⟨by simp [ext], hr ρ⟩
  refine (measure_apply_singleton (b.observes i) σ ρ).trans ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton ρ),
    cond_apply (Set.to_countable _).measurableSet, hset, hmass, measure_apply_singleton, hext]
  show ((b.weight (Function.updateFinset σ (b.uncertain.erase i) ρ) /
    b.weight.sumOver (b.uncertain.erase i) (Function.updateFinset σ (b.uncertain.erase i) ρ) :
      ℝ≥0) : ℝ≥0∞) = _
  rw [Factor.sumOver_updateFinset]
  by_cases h : b.weight.sumOver (b.uncertain.erase i) σ = 0
  · have h0 : b.weight (Function.updateFinset σ (b.uncertain.erase i) ρ) = 0 :=
      Finset.sum_eq_zero_iff.1 h ρ (Finset.mem_univ ρ)
    simp [h, h0]
  · rw [ENNReal.coe_div h, ENNReal.div_eq_inv_mul]

/-- The measure after a choice is the joint measure of the measure before it and the kernel of
the choice, if the factor of the belief does not depend on the new choice. -/
theorem measure_chooses {i : ι} (hi : i ∉ b.uncertain)
    (hbi : ∀ σ (τ : ∀ j : ({i} : Finset ι), X j),
      b.weight (Function.updateFinset σ {i} τ) = b.weight σ) (w : Factor X ℝ≥0) :
    (b.chooses i w).measure σ =
      ((b.measure σ) ⊗ₘ Kernel.ofFunOfCountable fun τ ↦
        ((choice i w).measure (Function.updateFinset σ b.uncertain τ) :
          Measure (∀ j : ({i} : Finset ι), X j))).map
        (Equiv.piFinsetUnion X (Finset.disjoint_singleton_right.2 hi)) := by
  classical
  have hd : Disjoint b.uncertain {i} := Finset.disjoint_singleton_right.2 hi
  refine Measure.ext_of_singleton (α := ∀ j : (b.uncertain ∪ {i} : Finset ι), X j) fun ρ ↦ ?_
  obtain ⟨⟨τ, x⟩, rfl⟩ := (Equiv.piFinsetUnion X hd).surjective ρ
  have hpre : (Equiv.piFinsetUnion X hd) ⁻¹' {Equiv.piFinsetUnion X hd (τ, x)} = {(τ, x)} := by
    ext p
    simp
  refine (measure_apply_singleton (b.chooses i w) σ _).trans ?_
  show ((b.weight * (w / w.sumOver {i})) (Function.updateFinset σ (b.uncertain ∪ {i})
    (Equiv.piFinsetUnion X hd (τ, x))) : ℝ≥0∞) = _
  rw [← Function.updateFinset_updateFinset hd, Pi.mul_apply, hbi]
  have hk : (choice i w).measure (Function.updateFinset σ b.uncertain τ) {x} =
      ((w / w.sumOver {i}) (Function.updateFinset (Function.updateFinset σ b.uncertain τ) {i} x) :
        ℝ≥0) :=
    measure_apply_singleton (choice i w) _ x
  have : IsFiniteKernel (Kernel.ofFunOfCountable fun τ : (∀ j : b.uncertain, X j) ↦
      ((choice i w).measure (Function.updateFinset σ b.uncertain τ) :
        Measure (∀ j : ({i} : Finset ι), X j))) :=
    ⟨⟨∑ τ, (choice i w).measure (Function.updateFinset σ b.uncertain τ) Set.univ,
      ENNReal.sum_lt_top.2 fun _ _ ↦ (measure_univ (choice i w) _).trans_lt ENNReal.coe_lt_top,
      fun τ ↦
      Finset.single_le_sum
        (f := fun τ ↦ (choice i w).measure (Function.updateFinset σ b.uncertain τ) Set.univ)
        (fun _ _ ↦ zero_le) (Finset.mem_univ τ)⟩⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpre,
    Measure.compProd_apply (measurableSet_singleton _), measure, lintegral_toMeasure,
    Finset.sum_eq_single τ]
  · have : Prod.mk τ ⁻¹' {(τ, x)} = ({x} : Set (∀ j : ({i} : Finset ι), X j)) := by ext; simp
    rw [this]
    refine Eq.trans ?_ (congrArg
      (· * (b.weight (Function.updateFinset σ b.uncertain τ) : ℝ≥0∞)) hk.symm)
    rw [← ENNReal.coe_mul, mul_comm]
  · intro τ' _ hτ'
    have : Prod.mk τ' ⁻¹' {(τ, x)} = (∅ : Set (∀ j : ({i} : Finset ι), X j)) := by
      ext; simp [hτ']
    simp [this]
  · simp

end Memo.Belief
