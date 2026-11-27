/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program.Belief
public import Minimemo.Belief.Measure

/-!
# Steps as operations on measures

This file states the action of the steps of a program in the terms of probability theory.

The numbers are nonnegative real numbers. The table that a `chooses` step adds has, as its
measure, the joint measure of the measure of the table before it and the kernel of the choice. The
table that an `observes` step adds has the measure of the table before it conditioned on the
observed value.

## Main results

* `Memo.Step.measure_chooses`: the measure of the table of a `chooses` step.
* `Memo.Step.measure_observes`: the measure of the table of an `observes` step.
* `Memo.Term.lintegral_expect`: the table of an expectation term is an integral.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Memo.Step

variable {D : Type} {F : ℕ → Type} {J : Interp D F ℝ≥0} {size : ℕ → ℕ}
  {W : Array (Table ℝ≥0)} (hW : ∀ x ∈ W, x.Sized size) (w : ℕ) (u : Finset ℕ)
include hW

/-- The measure of the table of a `chooses` step is the joint measure of the measure of the table
before it and the kernel of the choice, if the choice is new: it is not uncertain and is not a
variable of the table before. -/
theorem measure_chooses (i : ℕ) (t : Term D F) (hi : i ∉ u)
    (hiw : i ∉ (W.getD w (.const 1)).vars.map (·.1)) (σ : ∀ i, Fin (size i)) :
    (Table.toBelief size (u ∪ {i}) ((Step.chooses w [i] t).table J size W)).measure σ =
      ((Table.toBelief size u (W.getD w (.const 1))).measure σ ⊗ₘ
        Kernel.ofFunOfCountable fun τ ↦
          ((Belief.choice i (Table.toFactor size (t.eval J size W))).measure
            (Function.updateFinset σ u τ) : Measure (∀ j : ({i} : Finset ℕ), Fin (size j)))).map
        (Equiv.piFinsetUnion (fun i ↦ Fin (size i)) (Finset.disjoint_singleton_right.2 hi)) :=
  (Belief.measure_congr (congrArg Belief.weight (toBelief_chooses hW w u i t)) σ).trans
    (Belief.measure_chooses (Table.toBelief size u (W.getD w (.const 1))) σ hi
      (fun σ τ ↦ Table.toFactor_updateFinset_singleton hiw σ τ)
      (Table.toFactor size (t.eval J size W)))

/-- The measure of the table of an `observes` step is the measure of the table before it
conditioned on the observed value, with the observed choice forgotten. -/
theorem measure_observes (i : ℕ) (I : List ℕ) (hI : I.Nodup) (hu : I.toFinset = u.erase i)
    (hi : i ∈ u) (σ : ∀ i, Fin (size i)) :
    (Table.toBelief size (u.erase i) ((Step.observes w I).table J size W)).measure σ =
      (((Table.toBelief size u (W.getD w (.const 1))).measure σ)[|{τ | τ ⟨i, hi⟩ = σ i}]).map
        (Finset.restrict₂ (π := fun i ↦ Fin (size i)) (Finset.erase_subset i u)) :=
  (Belief.measure_congr (congrArg Belief.weight (toBelief_observes hW w u i I hI hu)) σ).trans
    (Belief.measure_observes (Table.toBelief size u (W.getD w (.const 1))) σ hi)

end Memo.Step

namespace Memo.Term

variable {D : Type} {F : ℕ → Type} {J : Interp D F ℝ≥0} {size : ℕ → ℕ}
  {W : Array (Table ℝ≥0)} (hW : ∀ x ∈ W, x.Sized size)
include hW

/-- The table of an expectation term is the integral of the factor of its term against the measure
of the belief that it names. -/
theorem lintegral_expect (w : ℕ) (I : List ℕ) (hI : I.Nodup) (t : Term D F)
    (σ : ∀ i, Fin (size i)) :
    ∫⁻ τ, ((Table.toFactor size (t.eval J size W) (Function.updateFinset σ I.toFinset τ) : ℝ≥0) :
        ℝ≥0∞) ∂(Table.toBelief size I.toFinset (W.getD w (.const 1))).measure σ =
      (Table.toFactor size ((Term.expect w I t).eval J size W) σ : ℝ≥0) := by
  rw [Term.toFactor_expect hW w I hI t]
  exact Belief.lintegral_measure _ σ _

end Memo.Term
