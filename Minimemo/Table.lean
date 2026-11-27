/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Defs.LinearOrder

/-!
# Tables

This file defines the arrays of memo as stored tables.

Every variable has a size, given once by a function `size`. A table has a list of variables and
one number for every assignment of a position below its size to each of them. The numbers are
stored in an array, in row-major order, so each is computed once. A table is read at an assignment
of positions to all variables; it ignores the variables that are not its own.

## Main definitions

* `Memo.Table K`: a list of variables and an array of numbers.
* `Memo.Table.get size t σ`: the number of the table `t` at the assignment `σ`.
* `Memo.Table.ofFn size vars f`: the table on `vars` with the values of the function `f`.
* `Memo.Table.const k`: the table with no variables and the number `k`.
* `Memo.Table.op size f ts`: the table that combines the numbers of the tables `ts` with `f`.
* `Memo.Table.sumOver size I t`: the table `t` summed over the variables in `I`.
* `Memo.Table.best size i t`: the table with the number one where `t` is greatest along the
  variable `i`, and zero elsewhere.
* `Memo.Table.rename size links t`: the table `t` with each variable replaced by the variable
  that `links` gives it.
-/

@[expose] public section

namespace Memo

/-- A **table** has a list of variables and one number for every assignment of a position to each
variable, stored in row-major order. -/
structure Table (K : Type*) where
  /-- The variables of the table. -/
  vars : List ℕ
  /-- The numbers of the table, in row-major order. -/
  data : Array K
  deriving Repr

namespace Table

variable {K : Type*} (size : ℕ → ℕ)

/-- The lists of positions for variables of the given sizes, in row-major order. -/
def positions : List ℕ → List (List ℕ)
  | [] => [[]]
  | m :: ms => (List.range m).flatMap fun j ↦ (positions ms).map (j :: ·)

/-- The place in the array of an assignment of positions to the variables. -/
def index (vars : List ℕ) (σ : ℕ → ℕ) : ℕ := vars.foldl (fun at' i ↦ at' * size i + σ i) 0

/-- The number of a table at an assignment of a position to every variable. -/
def get [Zero K] (t : Table K) (σ : ℕ → ℕ) : K := t.data.getD (index size t.vars σ) 0

/-- The assignment that gives the variables `vars` the positions `js`, and zero elsewhere. -/
def assign (vars : List ℕ) (js : List ℕ) (i : ℕ) : ℕ := ((vars.zip js).lookup i).getD 0

/-- The table on the variables `vars` whose numbers are the values of `f`. -/
def ofFn (vars : List ℕ) (f : (ℕ → ℕ) → K) : Table K :=
  ⟨vars, ((positions (vars.map size)).map fun js ↦ f (assign vars js)).toArray⟩

/-- The table with no variables and the number `k`. -/
def const (k : K) : Table K := ⟨[], #[k]⟩

/-- A list of variables in increasing order with one more variable, unless the list has it. -/
def insertVar (i : ℕ) : List ℕ → List ℕ
  | [] => [i]
  | j :: js => if i < j then i :: j :: js else if i = j then j :: js else j :: insertVar i js

/-- The variables of a list, each once, in increasing order. -/
def distinct (xs : List ℕ) : List ℕ := xs.foldr insertVar []

/-- The table that combines the numbers of a family of tables with `f`. -/
def op [Zero K] {k : ℕ} (f : (Fin k → K) → K) (ts : Fin k → Table K) : Table K :=
  ofFn size (distinct ((List.finRange k).flatMap fun i ↦ (ts i).vars)) fun σ ↦
    f fun i ↦ (ts i).get size σ

/-- The table summed over the variable `i`. A table that does not have the variable is constant
in it, so the sum adds each number to itself as many times as the variable has positions. -/
def sumOut [Zero K] [Add K] (i : ℕ) (t : Table K) : Table K :=
  if i ∈ t.vars then
    ofFn size (t.vars.filter (· != i)) fun σ ↦
      (List.range (size i)).foldl (fun total j ↦ total + t.get size (Function.update σ i j)) 0
  else ⟨t.vars, t.data.map fun x ↦ (List.range (size i)).foldl (fun total _ ↦ total + x) 0⟩

/-- The table summed over the variables in `I`. -/
def sumOver [Zero K] [Add K] (I : List ℕ) (t : Table K) : Table K :=
  I.foldl (fun t i ↦ t.sumOut size i) t

/-- The table with the number one at the positions where `t` is greatest along the variable `i`,
and zero elsewhere. -/
def best [Zero K] [One K] [LinearOrder K] (i : ℕ) (t : Table K) : Table K :=
  ofFn size t.vars fun σ ↦
    if (List.range (size i)).all fun j ↦ t.get size (Function.update σ i j) ≤ t.get size σ
    then 1 else 0

/-- The table with each variable replaced by the variable that `links` gives it. Two variables
with the same replacement become one, and the table is read where they agree. -/
def rename [Zero K] (links : List (ℕ × ℕ)) (t : Table K) : Table K :=
  let r (i : ℕ) : ℕ := (links.lookup i).getD i
  if t.vars.all fun i ↦ r i == i then t
  else ofFn size (distinct (t.vars.map r)) fun σ ↦ t.get size fun i ↦ σ (r i)

end Table

end Memo
