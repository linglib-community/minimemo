/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Core.Belief
public import Minimemo.Tensor

/-!
# Tensors as factors

This file relates the tensors of the semantics to the factors of the core.

A tensor is a function of an assignment of a position to every axis. Given a size for every axis,
the choices are the axes, and the values of the choice `i` are the positions below the size of
`i`. A tensor then gives a factor, and the sum of a tensor along an axis is the sum of its factor
over that choice.

## Main definitions

* `Memo.Tensor.toFactor size t`: the factor of the tensor `t` on the choices with the given sizes.

## Main results

* `Memo.Tensor.toFactor_sumAxis`: the factor of the sum along the axis `i` is the sum of the
  factor over the choice `i`.
-/

@[expose] public section

namespace Memo.Tensor

open Core

variable {K : Type*} [Semifield K] (size : ℕ → ℕ)

/-- The **factor of a tensor** on the choices whose values are the positions below the given
sizes. -/
def toFactor (t : Tensor K) : Factor (fun i ↦ Fin (size i)) K := fun σ ↦ t fun i ↦ σ i

@[simp] theorem toFactor_mul (s t : Tensor K) :
    toFactor size (s * t) = toFactor size s * toFactor size t := rfl

@[simp] theorem toFactor_div (s t : Tensor K) :
    toFactor size (s / t) = toFactor size s / toFactor size t := rfl

/-- The factor of the sum of a tensor along an axis is the sum of its factor over that choice. -/
theorem toFactor_sumAxis (i : ℕ) (t : Tensor K) :
    toFactor size (sumAxis i (size i) t) = (toFactor size t).sumOver {i} := by
  funext σ
  simp only [toFactor, sumAxis_apply, Factor.sumOver]
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ t (Function.update (fun k ↦ (σ k : ℕ)) i j)) (size i)]
  refine Fintype.sum_equiv (Equiv.piUnique (fun j : ({i} : Finset ℕ) ↦ Fin (size j))).symm _ _ ?_
  intro x
  congr 1
  funext k
  by_cases h : k = i
  · subst h
    have hx : ∀ j : ({k} : Finset ℕ),
        ((uniqueElim x : ∀ j : ({k} : Finset ℕ), Fin (size j)) j : ℕ) = x := by
      intro j
      obtain rfl : j = default := Subsingleton.elim _ _
      rw [uniqueElim_default]
    simpa [Function.updateFinset] using (hx _).symm
  · simp [Function.updateFinset, h]

end Memo.Tensor
