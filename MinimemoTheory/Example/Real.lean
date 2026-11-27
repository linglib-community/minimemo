/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Example.NaiveListener
public import MinimemoTheory.Transfer
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The naive listener with real numbers

This file proves that the naive listener returns, with real numbers, the array that it returns
with rational numbers.

Lean evaluates the model with rational numbers. The interpretations of the model with rational and
with real numbers are compatible along the inclusion of the rational numbers: the denotation
agrees on rational numbers. So the array with real numbers is the image of the array with rational
numbers.

## Main results

* `Memo.NaiveListener.compat`: the two interpretations are compatible.
* `Memo.NaiveListener.rows_real`: the array of the naive listener with real numbers.
-/

@[expose] public section

namespace Memo.NaiveListener

theorem denotesOf_cast (a b : ℚ) : denotesOf (a : ℝ) (b : ℝ) = ((denotesOf a b : ℚ) : ℝ) := by
  have h : ∀ (q : ℚ) (n : ℕ), ((q : ℝ) = (n : ℝ)) ↔ q = (n : ℚ) := fun q n ↦ by
    exact_mod_cast (Rat.cast_inj (α := ℝ) (p := q) (q := (n : ℚ)))
  have h0 := fun q ↦ h q 0
  have h1 := fun q ↦ h q 1
  have h2 := fun q ↦ h q 2
  have h3 := fun q ↦ h q 3
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at h0 h1 h2 h3
  unfold denotesOf
  simp only [h0, h1, h2, h3]
  split_ifs <;> simp

theorem countOf_cast (a : ℚ) : countOf (a : ℝ) = ((countOf a : ℚ) : ℝ) := by
  have h0 := denotesOf_cast a 0
  have h1 := denotesOf_cast a 1
  have h2 := denotesOf_cast a 2
  simp only [Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat] at h0 h1 h2
  simp only [countOf, h0, h1, h2, Rat.cast_add]

/-- The interpretations with rational and with real numbers are compatible along the inclusion of
the rational numbers. -/
theorem compat : Interp.Compat (Rat.castHom ℝ) (interpOf ℚ) (interpOf ℝ) :=
  Interp.compat_ofField Rat.cast_strictMono (fun d ↦ by cases d <;> rfl)
    (fun d j ↦ by cases d <;> simp [domOf]) fun f x ↦ by
      cases f
      · exact denotesOf_cast _ _
      · exact countOf_cast _

/-- The naive listener with real numbers returns the array of the naive listener: *green* and
*round* leave two referents equally likely, and *pink* and *square* pick out one. -/
theorem rows_real :
    Model.rows (interpOf ℝ) model =
      some [[1/2, 1/2, 0],
            [0,   0,   1],
            [1,   0,   0],
            [0,   1/2, 1/2]] := by
  have hq : Model.rows interp model =
      some [[1/2, 1/2, 0], [0, 0, 1], [1, 0, 0], [0, 1/2, 1/2]] := by decide +kernel
  rw [Model.rows_map Rat.cast_strictMono compat, hq]
  norm_num

end Memo.NaiveListener
