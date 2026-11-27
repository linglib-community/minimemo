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
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Memo.Step

variable {size : ℕ → ℕ} (W : Array (Table ℝ≥0)) (w : ℕ) (u : Finset ℕ)

/-- The measure of the table of a `chooses` step is the joint measure of the measure of the table
before it and the kernel of the choice, if the choice is new: it is not uncertain and is not a
variable of the table before. -/
theorem measure_chooses (i : ℕ) (t : Term ℝ≥0) (hw : (W.getD w (.const 1)).Sized size)
    (ht : (t.eval W).Sized size) (hi : i ∉ u) (hiw : i ∉ (W.getD w (.const 1)).vars.map (·.1))
    (σ : ∀ i, Fin (size i)) :
    (Table.toBelief size (u ∪ {i}) ((Step.chooses w [(i, size i)] t).table W)).measure σ =
      ((Table.toBelief size u (W.getD w (.const 1))).measure σ ⊗ₘ
        Kernel.ofFunOfCountable fun τ ↦
          ((Belief.choice i (Table.toFactor size (t.eval W))).measure
            (Function.updateFinset σ u τ) : Measure (∀ j : ({i} : Finset ℕ), Fin (size j)))).map
        (Equiv.piFinsetUnion (fun i ↦ Fin (size i)) (Finset.disjoint_singleton_right.2 hi)) := by
  exact (Belief.measure_congr (congrArg Belief.weight (toBelief_chooses W w u i t hw ht)) σ).trans
    (Belief.measure_chooses (Table.toBelief size u (W.getD w (.const 1))) σ hi
      (fun σ τ ↦ Table.toFactor_updateFinset_singleton hiw σ τ) (Table.toFactor size (t.eval W)))

/-- The measure of the table of an `observes` step is the measure of the table before it
conditioned on the observed value, with the observed choice forgotten. -/
theorem measure_observes (i : ℕ) (I : List ℕ) (hI : I.Nodup) (hu : I.toFinset = u.erase i)
    (hw : (W.getD w (.const 1)).Sized size) (hi : i ∈ u) (σ : ∀ i, Fin (size i)) :
    (Table.toBelief size (u.erase i)
        ((Step.observes w (I.map fun i ↦ (i, size i))).table W)).measure σ =
      (((Table.toBelief size u (W.getD w (.const 1))).measure σ)[|{τ | τ ⟨i, hi⟩ = σ i}]).map
        (Finset.restrict₂ (π := fun i ↦ Fin (size i)) (Finset.erase_subset i u)) := by
  exact (Belief.measure_congr (congrArg Belief.weight (toBelief_observes W w u i I hI hu hw))
    σ).trans (Belief.measure_observes (Table.toBelief size u (W.getD w (.const 1))) σ hi)

end Memo.Step
