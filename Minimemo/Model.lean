/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Compile
public import Minimemo.Term.Transfer

/-!
# The array of a model

This file defines the array that a model returns in an interpretation.

## Main definitions

* `Memo.Model.entries I M`: the entries of the array of `M`, in row-major order.
* `Memo.Model.rows I M`: the same entries, as rows along the last axis.

## Main results

* `Memo.Model.rows_map`: the rows of a model in two compatible interpretations.
-/

@[expose] public section

universe u

namespace Memo

variable {A N D : Type u} {F : ℕ → Type u} [DecidableEq A] [DecidableEq N] [DecidableEq D]

variable {K : Type u} [Semifield K] [LinearOrder K] (I : Interp D F K)

/-- The entries of the array of a model, in row-major order. -/
def Model.entries (M : Model A N D F) : Option (List K) := (Model.program M).map (·.entries I)

/-- The rows of the array of a model, along its last axis. -/
def Model.rows (M : Model A N D F) : Option (List (List K)) := (Model.program M).map (·.rows I)

/-- The rows of the array of a model in two compatible interpretations: those in the second are
the images of those in the first. -/
theorem Model.rows_map {L : Type u} [Semifield L] [LinearOrder L] {J : Interp D F L}
    {φ : K →+* L} (hφ : StrictMono φ) (h : Interp.Compat φ I J) (M : Model A N D F) :
    Model.rows J M = (Model.rows I M).map (List.map (List.map φ)) := by
  simp only [Model.rows, Option.map_map]
  congr 1
  funext p
  exact p.rows_map hφ h

end Memo
