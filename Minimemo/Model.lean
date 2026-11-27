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
* `Memo.Model.levels dom call M n`, `Memo.Model.level dom call M n`: the arrays of a family of
  models in which each may refer to the ones before it.
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

variable {K : Type u} [Zero K] [One K] [Add K] [LE K] [DecidableLE K] (I : Interp D F K)

/-- The entries of the array of a model, in row-major order. -/
def Model.entries (M : Model A N D F) : Option (List K) :=
  (Model.program M).toOption.map (·.entries I)

/-- The rows of the array of a model, along its last axis. -/
def Model.rows (M : Model A N D F) : Option (List (List K)) :=
  (Model.program M).toOption.map (·.rows I)

section Levels

variable {K : Type u} [Field K] [LinearOrder K]

/-- The entry of an array, with the given domains as its axes, at the positions of the values
`v 0`, `v 1`, …: the value of a model at those values of its axes. -/
def Model.lookup (doms : List (Domain K)) (entries : List K) (v : ℕ → K) : K :=
  entries.getD (doms.zipIdx.foldl (fun at' p ↦ at' * p.1.size + p.1.index (v p.2)) 0) 0

/-- The arrays of the first `n` models of a family in which a model may refer to the models before
it, as memo's models refer to themselves at a lower depth. The meaning of the outside functions
is `call ts` when `ts` holds the arrays of the models so far, so a reference to an earlier model
reads its array there. The arrays are computed from the first on, each once. -/
def Model.levels (dom : D → Domain K)
    (call : List (List K) → {k : ℕ} → F k → (Fin k → K) → K) (M : ℕ → Model A N D F) :
    ℕ → List (List K)
  | 0 => []
  | n + 1 =>
    let ts := Model.levels dom call M n
    ts ++ [(Model.entries (.ofField dom (call ts)) (M n)).getD []]

/-- The array of the model at depth `n` of a family, with the entries in row-major order. -/
def Model.level (dom : D → Domain K)
    (call : List (List K) → {k : ℕ} → F k → (Fin k → K) → K) (M : ℕ → Model A N D F) (n : ℕ) :
    List K :=
  (Model.levels dom call M (n + 1)).getLast?.getD []

end Levels

end Memo
