/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Measure
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Beliefs

This file gives the statements of memo a second meaning, on measures, and proves that it agrees
with their meaning on tables.

A belief gives, for each value of the choices that an agent knows, a measure on the values of the
choices that it is uncertain of. The statements of memo act on a belief as follows.

* `chooses` forms the joint measure of the belief and a kernel, the kernel of the choice.
* `observes` conditions the belief on the event that the observed choice has the observed value,
  and then forgets that choice.
* `E[e]` is the integral of `e` against the belief.

A table gives a belief: the measure at `k` gives the point `u` the mass that the table has at `k`
and `u`. This map is a bijection between tables and beliefs whose measures are finite, and it
sends each operation on tables to the operation on beliefs with the same name. So an array that
memo computes is the table of the belief that the same statements build from measures.

## Main definitions

* `Memo.Belief K U`: the type `K → Measure U` of beliefs.
* `Memo.Belief.normalize β`: the belief `fun k ↦ (β k)[|Set.univ]`.
* `Memo.Belief.chooses β η`: the belief `fun k ↦ β k ⊗ₘ η k`.
* `Memo.Belief.observes β`: the belief
  `fun (k, x) ↦ ((β k)[|Prod.snd ⁻¹' {x}]).map Prod.fst`.
* `Memo.Belief.expect β e`: the function `fun k ↦ ∫ u, e k u ∂β k`.
* `Memo.Table.toBelief π`: the belief `fun k ↦ toMeasure (π k)`.
* `Memo.Table.toKernel π`: the kernel of the belief of `π`, for a countable type of known values.
* `Memo.Table.equivBelief`: the bijection between tables and families of finite measures.

## Main results

* `Memo.Table.toBelief_normalize`: the belief of a normalized table is the normalized belief.
* `Memo.Table.toBelief_chooses`: the belief of the table after `chooses` is the joint measure of
  the belief and the kernel of the normalized weights.
* `Memo.Table.toBelief_observes`: the belief of the table after `observes` is the belief
  conditioned on the observed value.
* `Memo.Table.expect_eq`: the expectation in a table is the integral against its belief.

## Implementation notes

When an observed value has mass zero, the conditioned measure is the zero measure, and the table
after `observes` has a row of zeros there. The two agree, so the results need no hypothesis that
the observation is possible.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Memo

/-- A **belief** gives, for each value of the choices that an agent knows, a measure on the values
of the choices that it is uncertain of. -/
abbrev Belief (K U : Type*) [MeasurableSpace U] := K → Measure U

namespace Belief

variable {K K' U X : Type*} [MeasurableSpace U] [MeasurableSpace X]

/-- The **lift** of a belief along a function `f` is the belief whose measure at `k'` is the
measure of the belief at `f k'`. -/
def lift (f : K' → K) (β : Belief K U) : Belief K' U := fun k' ↦ β (f k')

/-- The **normalization** of a belief conditions each of its measures on the whole space, which
divides the measure by its total mass. -/
noncomputable def normalize (β : Belief K U) : Belief K U := fun k ↦ (β k)[|Set.univ]

/-- The belief after `chooses`: the joint measure of the belief and the kernel `η k`, which gives
the measure of the new choice at each value of the uncertain choices. -/
noncomputable def chooses (β : Belief K U) (η : K → Kernel U X) : Belief K (U × X) :=
  fun k ↦ β k ⊗ₘ η k

/-- The belief after `observes`: the measure at `k` is conditioned on the event that the observed
choice has the value `x`, and the observed choice is then forgotten. -/
noncomputable def observes (β : Belief K (U × X)) : Belief (K × X) U :=
  fun (k, x) ↦ ((β k)[|Prod.snd ⁻¹' {x}]).map Prod.fst

/-- The **expectation** of `e` in a belief is the integral of `e` against its measure. -/
noncomputable def expect (β : Belief K U) (e : K → U → ℝ) (k : K) : ℝ := ∫ u, e k u ∂β k

end Belief

namespace Table

variable {K K' U X : Type*} [MeasurableSpace U]

/-- The **belief of a table** gives, at each value `k` of the known choices, the measure in which
the point `u` has the mass that the table has at `k` and `u`. -/
noncomputable def toBelief (π : Table K U) : Belief K U := fun k ↦ toMeasure (π k)

@[simp] theorem toBelief_apply (π : Table K U) (k : K) : π.toBelief k = toMeasure (π k) := rfl

theorem toBelief_lift (f : K' → K) (π : Table K U) : (π.lift f).toBelief = π.toBelief.lift f :=
  rfl

variable [MeasurableSingletonClass U]

theorem toBelief_injective : Function.Injective (toBelief (K := K) (U := U)) := fun _ _ h ↦
  funext fun k ↦ toMeasure_injective (congrFun h k)



section Kernel

variable [MeasurableSpace K] [MeasurableSingletonClass K] [Countable K]

/-- The **kernel of a table** is the kernel whose measure at `k` is the measure of the belief of
the table at `k`. -/
noncomputable def toKernel (π : Table K U) : Kernel K U := Kernel.ofFunOfCountable π.toBelief

omit [MeasurableSingletonClass U] in
@[simp] theorem toKernel_apply (π : Table K U) (k : K) : π.toKernel k = toMeasure (π k) := rfl

end Kernel

variable [Fintype U] [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X]

instance (π : Table K U) (k : K) : IsFiniteMeasure (π.toBelief k) :=
  inferInstanceAs (IsFiniteMeasure (toMeasure (π k)))

/-- Tables correspond to the families of finite measures. -/
noncomputable def equivBelief : Table K U ≃ (K → FiniteMeasure U) :=
  Equiv.piCongrRight fun _ ↦ equivFiniteMeasure

@[simp] theorem coe_equivBelief (π : Table K U) (k : K) :
    (equivBelief π k : Measure U) = π.toBelief k := rfl

instance [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype K] (π : Table K U) :
    IsFiniteKernel π.toKernel :=
  ⟨⟨∑ k, toMeasure (π k) Set.univ, ENNReal.sum_lt_top.2 fun _ _ ↦ measure_lt_top _ _,
    fun k ↦ Finset.single_le_sum (f := fun k ↦ toMeasure (π k) Set.univ) (fun _ _ ↦ zero_le)
      (Finset.mem_univ k)⟩⟩

/-- The belief of a normalized table is the normalized belief. -/
theorem toBelief_normalize (w : Table K U) : w.normalize.toBelief = w.toBelief.normalize := by
  funext k
  refine Measure.ext_of_singleton fun u ↦ ?_
  simp only [toBelief_apply, Belief.normalize, toMeasure_apply_singleton, normalize_apply,
    cond_apply MeasurableSet.univ, Set.univ_inter, toMeasure_univ, ← ENNReal.ofNNReal_finsetSum]
  by_cases h : ∑ x', w k x' = 0
  · simp [h, (Finset.sum_eq_zero_iff.1 h) u (Finset.mem_univ u)]
  · rw [ENNReal.coe_div h, ENNReal.div_eq_inv_mul]

/-- The belief of the table after `chooses` is the joint measure of the belief of the table and
the kernel of the normalized weights. -/
theorem toBelief_chooses (π : Table K U) (w : Table (K × U) X) :
    (π.chooses w).toBelief =
      π.toBelief.chooses fun k ↦ (normalize fun u ↦ w (k, u)).toKernel := by
  funext k
  refine Measure.ext_of_singleton fun ⟨u, x⟩ ↦ ?_
  simp only [toBelief_apply, Belief.chooses, toMeasure_apply_singleton, chooses_apply,
    Measure.compProd_apply (measurableSet_singleton (u, x)), lintegral_toMeasure, toKernel_apply]
  rw [Finset.sum_eq_single u]
  · have : Prod.mk u ⁻¹' {(u, x)} = ({x} : Set X) := by ext; simp
    rw [this, toMeasure_apply_singleton, ENNReal.coe_mul, mul_comm]
    rfl
  · intro a _ ha
    have : Prod.mk a ⁻¹' {(u, x)} = (∅ : Set X) := by ext; simp [ha]
    simp [this]
  · simp

/-- The belief of the table after `observes` is the belief of the table conditioned on the observed
value, with the observed choice forgotten. -/
theorem toBelief_observes (π : Table K (U × X)) : π.observes.toBelief = π.toBelief.observes := by
  funext ⟨k, x⟩
  refine Measure.ext_of_singleton fun u ↦ ?_
  have hset : Prod.snd ⁻¹' {x} ∩ Prod.fst ⁻¹' {u} = ({(u, x)} : Set (U × X)) := by
    ext ⟨a, b⟩; simp [and_comm]
  have hmass : toMeasure (π k) (Prod.snd ⁻¹' {x}) = ((∑ u', π k (u', x) : ℝ≥0) : ℝ≥0∞) := by
    classical
    rw [toMeasure_apply, ENNReal.ofNNReal_finsetSum, Finset.sum_filter, Fintype.sum_prod_type]
    simp
  show toMeasure (π.observes (k, x)) {u} = ((toMeasure (π k))[|Prod.snd ⁻¹' {x}]).map Prod.fst {u}
  rw [toMeasure_apply_singleton, observes_apply,
    Measure.map_apply measurable_fst (measurableSet_singleton u),
    cond_apply (measurable_snd (measurableSet_singleton x)), hset, toMeasure_apply_singleton, hmass]
  by_cases h : ∑ u', π k (u', x) = 0
  · simp [h, (Finset.sum_eq_zero_iff.1 h) u (Finset.mem_univ u)]
  · rw [ENNReal.coe_div h, ENNReal.div_eq_inv_mul]

/-- The expectation in a table is the integral against the belief of the table. -/
theorem expect_eq (π : Table K U) (e : K → U → ℝ) : π.expect e = π.toBelief.expect e :=
  funext fun _ ↦ (integral_toMeasure _ _).symm

end Table

end Memo
