/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Example.NaiveListener
public import Minimemo.Program.Map
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# The naive listener with real numbers

This file proves that the naive listener with real numbers returns the array that the naive
listener with rational numbers returns.

Lean evaluates the model with rational numbers. The program of the model with real numbers is
related to the program with rational numbers along the inclusion of the rational numbers in the
real numbers: the two have the same steps, and the denotation and the test of equality agree on
rational numbers. So the array with real numbers is the image of the array with rational numbers.

## Main results

* `Memo.NaiveListener.rel`: the programs with rational and with real numbers are related.
* `Memo.NaiveListener.rows_real`: the array of the naive listener with real numbers.
-/

@[expose] public section

namespace Memo.NaiveListener

noncomputable section

/-- The steps of the program of the model with numbers in `K`. -/
def stepsOf (K : Type) [Field K] [LinearOrder K] : List (Step K) :=
  ((Model.program (domOf K) (modelOf K)).map (·.steps)).getD []

/-- The term that the program of the model with numbers in `K` returns. -/
def retOf (K : Type) [Field K] [LinearOrder K] : Term K :=
  ((Model.program (domOf K) (modelOf K)).map (·.ret)).getD (.lit 0)

/-- The program of the model, with numbers in any field. -/
theorem program_eq (K : Type) [Field K] [LinearOrder K] :
    Model.program (domOf K) (modelOf K) = some ⟨[4, 3, 3, 4, 3], stepsOf K, retOf K, [0, 1]⟩ :=
  rfl

theorem eqOf_cast (a b : ℚ) : eqOf (a : ℝ) (b : ℝ) = ((eqOf a b : ℚ) : ℝ) := by
  unfold eqOf
  split_ifs <;> simp_all

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

/-- The program of the model with real numbers is related to the program with rational numbers,
along the inclusion of the rational numbers. -/
theorem rel : Program.Rel (Rat.castHom ℝ) ⟨[4, 3, 3, 4, 3], stepsOf ℚ, retOf ℚ, [0, 1]⟩
    ⟨[4, 3, 3, 4, 3], stepsOf ℝ, retOf ℝ, [0, 1]⟩ := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;>
  repeat' first
    | exact fun x ↦ denotesOf_cast _ _
    | exact fun x ↦ eqOf_cast _ _
    | exact fun j ↦ (Rat.cast_natCast j).symm
    | exact Rat.cast_one.symm
    | constructor
    | (intro i; fin_cases i)

/-- The naive listener with real numbers returns the array of the naive listener: *green* and
*round* leave two referents equally likely, and *pink* and *square* pick out one. -/
theorem rows_real :
    Model.rows (domOf ℝ) (modelOf ℝ) =
      some [[1/2, 1/2, 0],
            [0,   0,   1],
            [1,   0,   0],
            [0,   1/2, 1/2]] := by
  have hq : (⟨[4, 3, 3, 4, 3], stepsOf ℚ, retOf ℚ, [0, 1]⟩ : Program ℚ).rows =
      [[1/2, 1/2, 0], [0, 0, 1], [1, 0, 0], [0, 1/2, 1/2]] := by decide +kernel
  show some (⟨[4, 3, 3, 4, 3], stepsOf ℝ, retOf ℝ, [0, 1]⟩ : Program ℝ).rows = _
  rw [rel.rows (Rat.cast_strictMono (K := ℝ)), hq]
  norm_num

end

end Memo.NaiveListener
