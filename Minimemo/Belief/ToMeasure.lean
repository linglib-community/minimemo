/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Rows of a table as measures

This file relates a row of a table to a measure. Let `U` be a finite type in which every singleton
is measurable. A function `p : U → ℝ≥0` gives the measure `Memo.toMeasure p`, in which the point `u`
has mass `p u`. A finite measure `μ` on `U` gives the function `Memo.ofMeasure μ`, which sends `u`
to the mass of `{u}`. The two maps are inverse to each other.

## Main definitions

* `Memo.toMeasure p`: the measure `∑ u, p u • dirac u`.
* `Memo.ofMeasure μ`: the function `fun u ↦ (μ {u}).toNNReal`.
* `Memo.equivFiniteMeasure`: the bijection between functions `U → ℝ≥0` and finite measures on `U`.

## Main results

* `Memo.toMeasure_apply_singleton`: the measure `toMeasure p` gives the point `u` the mass `p u`.
* `Memo.lintegral_toMeasure`, `Memo.integral_toMeasure`: an integral against `toMeasure p` is the
  sum of the values of the integrand weighted by `p`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Memo

variable {U : Type*} [MeasurableSpace U]

/-- The measure of a function `p : U → ℝ≥0` gives each point `u` the mass `p u`. -/
noncomputable def toMeasure (p : U → ℝ≥0) : Measure U :=
  Measure.sum fun u ↦ (p u : ℝ≥0∞) • Measure.dirac u

/-- The **point masses** of a measure `μ` form the function that sends `u` to the mass of `{u}`. -/
noncomputable def ofMeasure (μ : Measure U) : U → ℝ≥0 := fun u ↦ (μ {u}).toNNReal

variable [MeasurableSingletonClass U]

@[simp] theorem toMeasure_apply_singleton (p : U → ℝ≥0) (u : U) : toMeasure p {u} = p u :=
  Measure.sum_smul_dirac_singleton

theorem toMeasure_injective : Function.Injective (toMeasure (U := U)) := fun p q h ↦
  funext fun u ↦ by simpa using congrArg (· {u}) h

@[simp] theorem ofMeasure_toMeasure (p : U → ℝ≥0) : ofMeasure (toMeasure p) = p :=
  funext fun u ↦ by simp [ofMeasure]

variable [Fintype U]

/-- The measure `toMeasure p` of a set is the sum of `p` over the set. -/
theorem toMeasure_apply (p : U → ℝ≥0) (s : Set U) [DecidablePred (· ∈ s)] :
    toMeasure p s = ∑ u with u ∈ s, (p u : ℝ≥0∞) :=
  calc toMeasure p s
      = toMeasure p ((Finset.univ.filter (· ∈ s) : Finset U) : Set U) := by simp
    _ = ∑ u with u ∈ s, toMeasure p {u} := sum_measure_singleton.symm
    _ = ∑ u with u ∈ s, (p u : ℝ≥0∞) := by simp

theorem toMeasure_univ (p : U → ℝ≥0) : toMeasure p Set.univ = ∑ u, (p u : ℝ≥0∞) := by
  simp [toMeasure_apply]

instance (p : U → ℝ≥0) : IsFiniteMeasure (toMeasure p) :=
  ⟨by rw [toMeasure_univ]; exact ENNReal.sum_lt_top.2 fun _ _ ↦ ENNReal.coe_lt_top⟩

@[simp] theorem toMeasure_ofMeasure (μ : Measure U) [IsFiniteMeasure μ] :
    toMeasure (ofMeasure μ) = μ :=
  Measure.ext_of_singleton fun u ↦ by simp [ofMeasure, ENNReal.coe_toNNReal (measure_ne_top μ _)]

/-- Functions `U → ℝ≥0` on a finite type correspond to the finite measures on it. -/
noncomputable def equivFiniteMeasure : (U → ℝ≥0) ≃ FiniteMeasure U where
  toFun p := ⟨toMeasure p, inferInstance⟩
  invFun μ := ofMeasure μ
  left_inv := ofMeasure_toMeasure
  right_inv μ := Subtype.ext (toMeasure_ofMeasure (μ : Measure U))

@[simp] theorem coe_equivFiniteMeasure (p : U → ℝ≥0) :
    (equivFiniteMeasure p : Measure U) = toMeasure p := rfl

theorem lintegral_toMeasure (p : U → ℝ≥0) (f : U → ℝ≥0∞) :
    ∫⁻ u, f u ∂toMeasure p = ∑ u, f u * p u := by
  simp [lintegral_fintype]

theorem integral_toMeasure (p : U → ℝ≥0) (f : U → ℝ) :
    ∫ u, f u ∂toMeasure p = ∑ u, p u * f u := by
  rw [integral_countable .of_finite, tsum_fintype]
  simp [measureReal_def]

end Memo
