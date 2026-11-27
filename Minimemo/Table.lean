/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.NNReal.Basic

/-!
# Tables

This file defines the tables of the memo language and the operations that its statements perform
on them. In memo each agent has a frame of mind. The frame records the choices the agent knows and
the choices it is uncertain of, and it holds an array with one axis for each choice. An entry of
the array is the probability of some values of the uncertain choices, given some values of the
known ones.

Let `K` be the type of values of the known choices and `U` the type of values of the uncertain
ones. A table is a function `K → U → ℝ≥0`. The statements of memo act on a table as follows.

* `chooses` adds an uncertain choice with values in `X`. It multiplies each entry by a weight for
  each value of the new choice, after the weights have been normalized to sum to one.
* `observes` makes one uncertain choice known. It divides each entry by the sum of the entries
  that have the same values of the known choices and of the observed one.
* `E[e]` is the sum of the values of `e` weighted by the entries of the table.

For example, a listener thinks that a speaker chooses a referent `r` uniformly and then an
utterance `u` with weight `w r u`. The listener's table has the entries
`(1 / n) * (w r u / ∑ u', w r u')`, where `n` is the number of referents. When the listener
observes the utterance, the entry for `r` becomes its share of the entries with that utterance,
which is the posterior probability of `r`.

## Main definitions

* `Memo.Table K U`: the type `K → U → ℝ≥0` of tables.
* `Memo.Table.normalize w`: the table `fun k x ↦ w k x / ∑ x', w k x'`.
* `Memo.Table.chooses π w`: the table `fun k (u, x) ↦ π k u * w.normalize (k, u) x`.
* `Memo.Table.observes π`: the normalization of the table `fun (k, x) u ↦ π k (u, x)`.
* `Memo.Table.expect π e`: the function `fun k ↦ ∑ u, π k u * e k u`.
* `Memo.Table.lift f π`: the table `fun k' ↦ π (f k')`.

## Main results

* `Memo.Table.sum_normalize`: a row of a normalized table sums to one, or to zero if the row of
  weights is zero.

## Implementation notes

The paper gives the semantics on arrays whose axes are numbered by a global counter, and it uses
broadcasting to combine arrays with different axes. Here the axes of a table are the components of
the types `K` and `U`, so a choice is added by a product of types and no axis is numbered.

An entry is a nonnegative real number, and division by zero gives zero, so a row of weights that
sums to zero gives a row of zeros. The expectation sums over all the uncertain choices of the
frame.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*, Proc. ACM Program.
  Lang. 9, OOPSLA2, Article 300 (2025)
-/

@[expose] public section

open scoped NNReal

namespace Memo

/-- A **table** gives, for each value of the choices that an agent knows, a weight for each value
of the choices that it is uncertain of. -/
abbrev Table (K U : Type*) := K → U → ℝ≥0

namespace Table

variable {K K' U X : Type*}

/-- The **lift** of a table along a function `f` is the table whose row at `k'` is the row of the
table at `f k'`. It reads the table of an agent from the frame of an agent who models it, where
`f` gives what the modelled agent knows. -/
def lift (f : K' → K) (π : Table K U) : Table K' U := fun k' ↦ π (f k')

@[simp] theorem lift_apply (f : K' → K) (π : Table K U) (k' : K') : π.lift f k' = π (f k') := rfl

section Normalize

variable [Fintype X]

/-- The **normalization** of a table divides each entry by the sum of its row. A row of zeros
stays a row of zeros. -/
noncomputable def normalize (w : Table K X) : Table K X := fun k x ↦ w k x / ∑ x', w k x'

theorem normalize_apply (w : Table K X) (k : K) (x : X) :
    w.normalize k x = w k x / ∑ x', w k x' := rfl

/-- A row of a normalized table sums to one, or to zero if the row of weights is zero. -/
theorem sum_normalize (w : Table K X) (k : K) :
    ∑ x, w.normalize k x = if ∑ x, w k x = 0 then 0 else 1 := by
  simp only [normalize_apply, ← Finset.sum_div]
  split_ifs with h
  · rw [h, div_zero]
  · exact div_self h

theorem sum_normalize_le_one (w : Table K X) (k : K) : ∑ x, w.normalize k x ≤ 1 := by
  rw [sum_normalize]; split_ifs <;> simp

/-- A normalized table is its own normalization. -/
@[simp] theorem normalize_normalize (w : Table K X) : w.normalize.normalize = w.normalize := by
  funext k x
  rw [normalize_apply, sum_normalize]
  split_ifs with h
  · rw [div_zero, normalize_apply, h, div_zero]
  · rw [div_one]

end Normalize

/-- The table after `chooses`: a new uncertain choice with values in `X` is added, and each entry
is multiplied by the normalized weight `w` of the value chosen. This is equation (1) of the
paper. -/
noncomputable def chooses [Fintype X] (π : Table K U) (w : Table (K × U) X) : Table K (U × X) :=
  fun k (u, x) ↦ π k u * w.normalize (k, u) x

@[simp] theorem chooses_apply [Fintype X] (π : Table K U) (w : Table (K × U) X) (k : K) (u : U)
    (x : X) : π.chooses w k (u, x) = π k u * w.normalize (k, u) x := rfl

/-- The table after `observes`: the choice with values in `X` becomes known, and each entry is
divided by the sum of the entries with the same known and observed values. This is equation (2)
of the paper. -/
noncomputable def observes [Fintype U] (π : Table K (U × X)) : Table (K × X) U :=
  normalize fun (k, x) u ↦ π k (u, x)

@[simp] theorem observes_apply [Fintype U] (π : Table K (U × X)) (k : K) (x : X) (u : U) :
    π.observes (k, x) u = π k (u, x) / ∑ u', π k (u', x) := rfl

/-- The **expectation** of `e` in a table is the sum of the values of `e` weighted by the entries
of the table. -/
noncomputable def expect [Fintype U] (π : Table K U) (e : K → U → ℝ) (k : K) : ℝ :=
  ∑ u, π k u * e k u

end Table

end Memo
