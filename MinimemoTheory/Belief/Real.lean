/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Belief.Measure
public import Mathlib.Basic.NNReal.Basic

/-!
# Beliefs with real numbers

This file gives a belief with real numbers its measures.

The numbers of a model are real: a utility or a logarithm can be negative. The factor of a belief
is a probability, so it is nonnegative, and that is a hypothesis here and not the type of the
numbers. A belief with a nonnegative real factor has the measures of the same belief with
nonnegative real numbers, `Memo.Belief.toNNReal`. The statements of memo act on them as on the
measures of that belief, and the expectation of a real factor, of either sign, is its integral.

## Main definitions

* `Memo.Belief.toNNReal b`: the belief with nonnegative real numbers that has the factor of `b`.

## Main results

* `Memo.Belief.chooses_nonneg`, `Memo.Belief.observes_nonneg`: the factor stays nonnegative.
* `Memo.Belief.toNNReal_chooses`, `Memo.Belief.toNNReal_observes`: the belief after a choice or an
  observation, with nonnegative real numbers.
* `Memo.Belief.integral_measure`: the expectation of a real factor is its integral.
* `Memo.Belief.measure_toNNReal_chooses`, `Memo.Belief.measure_toNNReal_observes`: the measure
  after a choice is a joint measure, and after an observation a conditioned measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Memo.Belief

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  {b : Belief X ℝ} {w : Factor X ℝ} {i : ι}

/-- The belief with nonnegative real numbers that has the factor of a belief with real numbers. A
negative number becomes zero. -/
abbrev toNNReal (b : Belief X ℝ) : Belief X ℝ≥0 := ⟨b.uncertain, fun σ ↦ (b.weight σ).toNNReal⟩

theorem sumOver_nonneg {f : Factor X ℝ} (hf : 0 ≤ f) (s : Finset ι) : 0 ≤ f.sumOver s :=
  fun _ ↦ Finset.sum_nonneg fun _ _ ↦ hf _

/-- The factor after a choice with a nonnegative weight is nonnegative. -/
theorem chooses_nonneg (hb : 0 ≤ b.weight) (hw : 0 ≤ w) : 0 ≤ (b.chooses i w).weight :=
  fun σ ↦ mul_nonneg (hb σ) (div_nonneg (hw σ) (sumOver_nonneg hw _ σ))

/-- The factor after an observation is nonnegative. -/
theorem observes_nonneg (hb : 0 ≤ b.weight) : 0 ≤ (b.observes i).weight :=
  fun σ ↦ div_nonneg (hb σ) (sumOver_nonneg hb _ σ)

theorem toNNReal_sumOver {f : Factor X ℝ} (hf : 0 ≤ f) (s : Finset ι) (σ : ∀ i, X i) :
    (f.sumOver s σ).toNNReal = Factor.sumOver s (fun σ ↦ (f σ).toNNReal) σ :=
  Real.toNNReal_sum_of_nonneg fun _ _ ↦ hf _

/-- The belief after a choice, with nonnegative real numbers. -/
theorem toNNReal_chooses (hb : 0 ≤ b.weight) (hw : 0 ≤ w) :
    (b.chooses i w).toNNReal = b.toNNReal.chooses i fun σ ↦ (w σ).toNNReal := by
  simp only [toNNReal, chooses]
  congr 1
  funext σ
  simp only [Pi.mul_apply, Pi.div_apply]
  rw [Real.toNNReal_mul (hb σ), Real.toNNReal_div (hw σ), toNNReal_sumOver hw]

/-- The belief after an observation, with nonnegative real numbers. -/
theorem toNNReal_observes (hb : 0 ≤ b.weight) :
    (b.observes i).toNNReal = b.toNNReal.observes i := by
  simp only [toNNReal, observes]
  congr 1
  funext σ
  simp only [Pi.div_apply]
  rw [Real.toNNReal_div (hb σ), toNNReal_sumOver hb]

variable [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

/-- The expectation of a real factor, of either sign, in a belief with a nonnegative factor is its
integral against the measure of the belief. -/
theorem integral_measure (hb : 0 ≤ b.weight) (e : Factor X ℝ) (σ : ∀ i, X i) :
    ∫ τ, e (Function.updateFinset σ b.uncertain τ) ∂(b.toNNReal.measure σ) = b.expect e σ := by
  rw [Belief.measure, integral_toMeasure]
  simp only [toNNReal, expect, Factor.sumOver, Pi.mul_apply, Real.coe_toNNReal _ (hb _), mul_comm]

/-- The measure after a choice with a nonnegative weight is the joint measure of the measure
before it and the kernel of the choice, if the factor does not depend on the new choice. -/
theorem measure_toNNReal_chooses (hb : 0 ≤ b.weight) (hw : 0 ≤ w) (hi : i ∉ b.uncertain)
    (hbi : ∀ σ (τ : ∀ j : ({i} : Finset ι), X j),
      b.weight (Function.updateFinset σ {i} τ) = b.weight σ) (σ : ∀ i, X i) :
    (b.chooses i w).toNNReal.measure σ =
      ((b.toNNReal.measure σ) ⊗ₘ Kernel.ofFunOfCountable fun τ ↦
        ((choice i fun σ ↦ (w σ).toNNReal).measure (Function.updateFinset σ b.uncertain τ) :
          Measure (∀ j : ({i} : Finset ι), X j))).map
        (Equiv.piFinsetUnion X (Finset.disjoint_singleton_right.2 hi)) :=
  (measure_congr (congrArg Belief.weight (toNNReal_chooses hb hw)) σ).trans
    (measure_chooses b.toNNReal σ hi (fun σ τ ↦ by simp only [hbi]) _)

/-- The measure after an observation is the measure before it conditioned on the observed value,
with the observed choice forgotten. -/
theorem measure_toNNReal_observes (hb : 0 ≤ b.weight) (hi : i ∈ b.uncertain) (σ : ∀ i, X i) :
    (b.observes i).toNNReal.measure σ =
      ((b.toNNReal.measure σ)[|{τ | τ ⟨i, hi⟩ = σ i}]).map
        (Finset.restrict₂ (Finset.erase_subset i b.uncertain)) :=
  (measure_congr (congrArg Belief.weight (toNNReal_observes hb)) σ).trans
    (measure_observes b.toNNReal σ hi)

end Memo.Belief
