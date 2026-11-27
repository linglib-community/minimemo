/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Tables

This file defines the arrays of memo as stored tables.

A table has a list of variables, each with a size, and one number for every assignment of a
position below its size to each of its variables. The numbers are stored in an array, in row-major
order, so each is computed once. A table is read at an assignment of positions to all variables;
it ignores the variables that are not its own.

## Main definitions

* `Memo.Core.Table K`: a list of variables with sizes and an array of numbers.
* `Memo.Core.Table.get t σ`: the number of the table `t` at the assignment `σ`.
* `Memo.Core.Table.ofFn vars f`: the table on `vars` with the values of the function `f`.
* `Memo.Core.Table.const k`: the table with no variables and the number `k`.
* `Memo.Core.Table.map₂ f s t`: the table that combines the numbers of `s` and `t` with `f`.
* `Memo.Core.Table.sumOut i t`: the table `t` summed over its variable `i`.
-/

@[expose] public section

namespace Memo.Core

/-- A **table** has a list of variables with their sizes and one number for every assignment of a
position to each variable, stored in row-major order. -/
structure Table (K : Type*) where
  /-- The variables of the table, each with its size. -/
  vars : List (ℕ × ℕ)
  /-- The numbers of the table, in row-major order. -/
  data : Array K
  deriving Repr

namespace Table

variable {K : Type*}

/-- The lists of positions for variables of the given sizes, in row-major order. -/
def positions : List ℕ → List (List ℕ)
  | [] => [[]]
  | m :: ms => (List.range m).flatMap fun j ↦ (positions ms).map (j :: ·)

/-- The place in the array of an assignment of positions to the variables. -/
def index (vars : List (ℕ × ℕ)) (σ : ℕ → ℕ) : ℕ := vars.foldl (fun at' v ↦ at' * v.2 + σ v.1) 0

/-- The number of a table at an assignment of a position to every variable. -/
def get [Zero K] (t : Table K) (σ : ℕ → ℕ) : K := t.data.getD (index t.vars σ) 0

/-- The assignment that gives the variables of `vars` the positions `js`, and zero elsewhere. -/
def assign (vars : List (ℕ × ℕ)) (js : List ℕ) (i : ℕ) : ℕ :=
  ((vars.map (·.1)).zip js).lookup i |>.getD 0

/-- The table on the variables `vars` whose numbers are the values of `f`. -/
def ofFn (vars : List (ℕ × ℕ)) (f : (ℕ → ℕ) → K) : Table K :=
  ⟨vars, ((positions (vars.map (·.2))).map fun js ↦ f (assign vars js)).toArray⟩

/-- The table with no variables and the number `k`. -/
def const (k : K) : Table K := ⟨[], #[k]⟩

/-- The variables of either of two lists, in increasing order. -/
def union (xs ys : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (xs ++ ys.filter fun y ↦ !xs.any (·.1 == y.1)).mergeSort fun a b ↦ a.1 ≤ b.1

/-- The table that combines the numbers of two tables with `f`. -/
def map₂ [Zero K] (f : K → K → K) (s t : Table K) : Table K :=
  ofFn (union s.vars t.vars) fun σ ↦ f (s.get σ) (t.get σ)

/-- The table summed over its variable `i`. -/
def sumOut [Zero K] [Add K] (i : ℕ) (t : Table K) : Table K :=
  match t.vars.find? (·.1 == i) with
  | none => t
  | some v =>
    ofFn (t.vars.filter (·.1 != i)) fun σ ↦
      (List.range v.2).foldl (fun total j ↦ total + t.get (Function.update σ i j)) 0

instance [Zero K] [Mul K] : Mul (Table K) := ⟨map₂ (· * ·)⟩
instance [Zero K] [Div K] : Div (Table K) := ⟨map₂ (· / ·)⟩

end Table

end Memo.Core
