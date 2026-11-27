/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Factors

This file defines the numbers of a model as functions of the choices.

The choices of a model are indexed by a type `ι`, and the choice `i` has values in `X i`. An
assignment gives every choice a value. A factor is a number that depends on the assignment.

## Main definitions

* `Memo.Factor X K`: the type `(∀ i, X i) → K` of factors.
* `Memo.Factor.sumOver s f`: the sum of `f` over the values of the choices in `s`.

## Main results

* `Memo.Factor.sumOver_union`: the sum over a union of two disjoint sets of choices is the sum
  over one of the sum over the other.
-/

@[expose] public section

namespace Memo

variable {ι : Type*} [DecidableEq ι] (X : ι → Type*) (K : Type*)

/-- A **factor** is a number that depends on the assignment of a value to every choice. -/
abbrev Factor := (∀ i, X i) → K

variable {X K} [∀ i, Fintype (X i)] [Semifield K]

/-- The **sum of a factor over a set of choices** adds its values at the assignments that agree
with the given one off that set. -/
def Factor.sumOver (s : Finset ι) (f : Factor X K) : Factor X K :=
  fun σ ↦ ∑ τ : ∀ i : s, X i, f (Function.updateFinset σ s τ)

omit [∀ i, Fintype (X i)] in
theorem Function.updateFinset_updateFinset_self (σ : ∀ i, X i) (s : Finset ι)
    (τ τ' : ∀ i : s, X i) :
    Function.updateFinset (Function.updateFinset σ s τ) s τ' = Function.updateFinset σ s τ' := by
  funext j
  by_cases h : j ∈ s <;> simp [Function.updateFinset, h]

/-- The sum of a factor over a set of choices does not depend on the values of those choices. -/
theorem Factor.sumOver_updateFinset (s : Finset ι) (f : Factor X K) (σ : ∀ i, X i)
    (τ : ∀ i : s, X i) : f.sumOver s (Function.updateFinset σ s τ) = f.sumOver s σ := by
  simp only [Factor.sumOver, Function.updateFinset_updateFinset_self]

/-- The sum over no choices is the factor. -/
@[simp] theorem Factor.sumOver_empty (f : Factor X K) : f.sumOver ∅ = f := by
  funext σ
  have : Unique (∀ i : (∅ : Finset ι), X i) := Pi.uniqueOfIsEmpty _
  rw [Factor.sumOver, Fintype.sum_unique]
  congr 1

/-- The sum over a union of two disjoint sets of choices is the sum over one of the sum over the
other. -/
theorem Factor.sumOver_union {s t : Finset ι} (hst : Disjoint s t) (f : Factor X K) :
    f.sumOver (s ∪ t) = (f.sumOver t).sumOver s := by
  funext σ
  simp only [Factor.sumOver, Function.updateFinset_updateFinset hst]
  rw [← (Equiv.piFinsetUnion X hst).sum_comp, Fintype.sum_prod_type]

end Memo
