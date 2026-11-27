/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Compile

/-!
# The array of a model

This file defines the array that a model returns in an interpretation.

## Main definitions

* `Memo.Model.error M`: why the model `M` is not accepted, if it is not.
* `Memo.Model.entries I M`: the entries of the array of `M`, in row-major order.
* `Memo.Model.rows I M`: the same entries, as rows along the last axis.
-/

@[expose] public section

universe u

namespace Memo

variable {A N D : Type u} {F : ℕ → Type u} [DecidableEq A] [DecidableEq N] [DecidableEq D]

/-- Why a model is not accepted, if it is not. -/
def Model.error (M : Model A N D F) : Option (Error A N) :=
  match Model.program M with
  | .error e => some e
  | .ok _ => none

variable {K : Type u} [Semifield K] [LinearOrder K] (I : Interp D F K)

/-- The entries of the array of a model, in row-major order. -/
def Model.entries (M : Model A N D F) : Option (List K) :=
  (Model.program M).toOption.map (·.entries I)

/-- The rows of the array of a model, along its last axis. -/
def Model.rows (M : Model A N D F) : Option (List (List K)) :=
  (Model.program M).toOption.map (·.rows I)

end Memo
