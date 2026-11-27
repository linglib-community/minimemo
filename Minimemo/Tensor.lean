/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Tensors

This file defines the arrays in which memo computes.

memo gives each choice an axis, numbered by a counter that all the agents share, and computes
with arrays that have one dimension for each axis. An array that does not vary along an axis has
size one there, and the operations stretch it to match the other operand. We represent such an
array as a function of an assignment, which gives a position on every axis. An array that does not
vary along an axis is a function that does not depend on the assignment there, so pointwise
operations on functions are the stretched operations on arrays.

## Main definitions

* `Memo.Domain K`: a finite sequence of numbers, the values that a choice can take.
* `Memo.Tensor K`: the type `(ℕ → ℕ) → K` of functions of an assignment.
* `Memo.Tensor.scalar r`: the tensor with the value `r` at every assignment.
* `Memo.Tensor.basis v i`: the tensor whose value is `v` at the position on the axis `i`.
* `Memo.Tensor.sumAxis i m z`: the sum of `z` over the first `m` positions on the axis `i`.
* `Memo.Tensor.sum I z`: the sum of `z` over the axes in `I`, each with its size.
* `Memo.Tensor.swapAxes i k z`: the tensor `z` with the axes `i` and `k` exchanged.
* `Memo.Tensor.rows z m n`: the entries of `z` on the first two axes, as a list of `m` rows of
  `n` numbers.
* `Memo.Tensor.entries z sizes`: the entries of `z` on its first axes, in row-major order.

## Main results

* `Memo.Tensor.sumAxis_update`: a sum over an axis does not depend on the position on that axis.
-/

@[expose] public section

namespace Memo

/-- A **domain** is a finite sequence of numbers, the values that a choice can take. -/
structure Domain (K : Type*) where
  /-- The number of values. -/
  size : ℕ
  /-- The value at each position. -/
  val : ℕ → K

/-- The first position at which a domain has the value `v`, or zero if it has none. -/
def Domain.index {K : Type*} [DecidableEq K] (X : Domain K) (v : K) : ℕ :=
  ((List.range X.size).find? fun j ↦ X.val j = v).getD 0

/-- A **tensor** is a function of an assignment, which gives a position on every axis, with values
in the numbers `K`. -/
abbrev Tensor (K : Type*) := (ℕ → ℕ) → K

namespace Tensor

variable {K : Type*}

/-- The **scalar** tensor of `r` has the value `r` at every assignment. -/
def scalar (r : K) : Tensor K := fun _ ↦ r

/-- The **basis** tensor of the values `v` along the axis `i` has, at each assignment, the value
of `v` at the position on the axis `i`. -/
def basis (v : ℕ → K) (i : ℕ) : Tensor K := fun σ ↦ v (σ i)

/-- The **sum along an axis** `i` of size `m` adds the values of a tensor at the first `m`
positions on that axis. -/
def sumAxis [AddCommMonoid K] (i m : ℕ) (z : Tensor K) : Tensor K :=
  fun σ ↦ ∑ j ∈ Finset.range m, z (Function.update σ i j)

/-- The **maximum along an axis** `i` of size `m` is the greatest of the values of a tensor at the
first `m` positions on that axis. -/
def maxAxis [LinearOrder K] (i m : ℕ) (z : Tensor K) : Tensor K :=
  fun σ ↦ ((List.range m).map fun j ↦ z (Function.update σ i j)).foldl max
    (z (Function.update σ i 0))

/-- The **sum along the axes** in `I`, a list of axes with their sizes, sums along each of them in
turn. -/
def sum [AddCommMonoid K] (I : List (ℕ × ℕ)) (z : Tensor K) : Tensor K :=
  I.foldr (fun p z ↦ sumAxis p.1 p.2 z) z

/-- The tensor with the axes `i` and `k` **swapped** has, at each assignment, the value of the
tensor at the assignment with the positions on `i` and `k` exchanged. -/
def swapAxes (i k : ℕ) (z : Tensor K) : Tensor K := fun σ ↦ z (σ ∘ Equiv.swap i k)

/-- The **entry** of a tensor at a list of positions, one for each of the first axes. -/
def entry (z : Tensor K) (js : List ℕ) : K := z fun i ↦ js.getD i 0

/-- The **rows** of a tensor on its first two axes, of sizes `m` and `n`: the array that a model
with two axes returns. -/
def rows (z : Tensor K) (m n : ℕ) : List (List K) :=
  (List.range m).map fun i ↦ (List.range n).map fun j ↦ z.entry [i, j]

/-- The lists of positions on axes of the given sizes, in row-major order. -/
def indices : List ℕ → List (List ℕ)
  | [] => [[]]
  | m :: ms => (List.range m).flatMap fun i ↦ (indices ms).map (i :: ·)

/-- The **entries** of a tensor on its first axes, of the given sizes, in row-major order. -/
def entries (z : Tensor K) (sizes : List ℕ) : List K := (indices sizes).map z.entry

variable (i k m : ℕ) (z : Tensor K) (σ : ℕ → ℕ)

@[simp] theorem scalar_apply (r : K) : scalar r σ = r := rfl

@[simp] theorem basis_apply (v : ℕ → K) : basis v i σ = v (σ i) := rfl

@[simp] theorem swapAxes_apply : swapAxes i k z σ = z (σ ∘ Equiv.swap i k) := rfl

@[simp] theorem swapAxes_swapAxes : swapAxes i k (swapAxes i k z) = z :=
  funext fun σ ↦ congrArg z (funext fun x ↦ by simp)

variable [AddCommMonoid K]

theorem sumAxis_apply : sumAxis i m z σ = ∑ j ∈ Finset.range m, z (Function.update σ i j) := rfl

@[simp] theorem sum_nil : sum [] z = z := rfl

@[simp] theorem sum_cons (p : ℕ × ℕ) (I : List (ℕ × ℕ)) :
    sum (p :: I) z = sumAxis p.1 p.2 (sum I z) := rfl

/-- A sum over an axis does not depend on the position on that axis. -/
@[simp] theorem sumAxis_update (j : ℕ) :
    sumAxis i m z (Function.update σ i j) = sumAxis i m z σ := by
  simp [sumAxis_apply]

end Tensor

end Memo
