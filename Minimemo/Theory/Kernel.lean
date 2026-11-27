/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Family
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Basic.Real.Basic

/-!
# The kernel of a model

This file reads the array of a model as a kernel, and says when two models are the same in what
they return.

A model returns an array. Its last axis is the choice that the model reports, and the other axes
are what the model is given: the array of a listener has a row for each utterance, and the row
gives a number to each referent. So the array is a kernel from the positions of its rows to the
positions along a row, whose measure at a row gives each position the number there. The kernel is
defined for every array: a number that is negative gives no mass.

Two models are equivalent when they have the same kernel. Models that differ in the order of
their statements, or in a constant factor of a weight, may be equivalent.

## Main definitions

* `Memo.rowsKernel rows`: the kernel of an array, given as its rows.
* `Memo.Model.kernel I M`: the kernel of the model `M`.
* `Memo.Family.kernel fam dom fn n p`: the kernel of a member of a family of models.
* `Memo.Model.Equiv I M₁ M₂`: the two models have the same kernel.

## Main results

* `Memo.rowsKernel_apply_singleton`: the mass of a position in a row is the number there.
* `Memo.Model.equiv_of_rows_eq`: models with the same array are equivalent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

universe u

namespace Memo

/-- The measure of a row of numbers: the position `j` has the mass of the number at `j`. -/
noncomputable def rowMeasure (row : List ℝ) : Measure ℕ :=
  Measure.sum fun j ↦ ENNReal.ofReal (row.getD j 0) • Measure.dirac j

theorem rowMeasure_apply_singleton (row : List ℝ) (j : ℕ) :
    rowMeasure row {j} = ENNReal.ofReal (row.getD j 0) :=
  Measure.sum_smul_dirac_singleton

/-- The **kernel of an array**, given as its rows: the measure at the row `i` gives the position
`j` the number at `j` in that row. -/
noncomputable def rowsKernel (rows : List (List ℝ)) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun i ↦ rowMeasure (rows.getD i [])

/-- The mass of a position in a row is the number there. -/
theorem rowsKernel_apply_singleton (rows : List (List ℝ)) (i j : ℕ) :
    rowsKernel rows i {j} = ENNReal.ofReal ((rows.getD i []).getD j 0) :=
  rowMeasure_apply_singleton _ j

variable {A N D : Type} {F : ℕ → Type} [DecidableEq A] [DecidableEq N] [DecidableEq D]

/-- The **kernel of a model**: the kernel of its array, from the positions of the rows to the
positions along the last axis. -/
noncomputable def Model.kernel (I : Interp D F ℝ) (M : Model A N D F) : Kernel ℕ ℕ :=
  rowsKernel ((Model.rows I M).getD [])

/-- Two models are **equivalent** in an interpretation when they have the same kernel. -/
def Model.Equiv (I : Interp D F ℝ) (M₁ M₂ : Model A N D F) : Prop := M₁.kernel I = M₂.kernel I

theorem Model.equiv_refl (I : Interp D F ℝ) (M : Model A N D F) : Model.Equiv I M M := rfl

theorem Model.Equiv.symm {I : Interp D F ℝ} {M₁ M₂ : Model A N D F} (h : Model.Equiv I M₁ M₂) :
    Model.Equiv I M₂ M₁ := Eq.symm h

theorem Model.Equiv.trans {I : Interp D F ℝ} {M₁ M₂ M₃ : Model A N D F}
    (h₁ : Model.Equiv I M₁ M₂) (h₂ : Model.Equiv I M₂ M₃) : Model.Equiv I M₁ M₃ :=
  Eq.trans h₁ h₂

/-- Models with the same array are equivalent. -/
theorem Model.equiv_of_rows_eq {I : Interp D F ℝ} {M₁ M₂ : Model A N D F}
    (h : Model.rows I M₁ = Model.rows I M₂) : Model.Equiv I M₁ M₂ := by
  rw [Model.Equiv, Model.kernel, Model.kernel, h]

/-- An array in row-major order, cut into rows of the size `n`. -/
def chunks (n : ℕ) (l : List ℝ) : List (List ℝ) :=
  (List.range (l.length / n)).map fun i ↦ (l.drop (i * n)).take n

variable {P R : Type} [BEq P]

/-- The **kernel of a member of a family** of models, where references are followed to the depth
`n`: the kernel of its array, cut into rows of the size of the last axis. -/
noncomputable def Family.kernel (fam : Family A N D F P R) (dom : D → Domain ℝ)
    (fn : {k : ℕ} → F k → (Fin k → ℝ) → ℝ) (n : ℕ) (p : P) : Kernel ℕ ℕ :=
  rowsKernel (chunks (((fam.model p).axes.getLast?.map fun a ↦ (dom a.2).size).getD 1)
    (fam.entries .ofField dom fn n p))

end Memo
