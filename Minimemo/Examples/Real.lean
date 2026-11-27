/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Theory.Kernel
public import Minimemo.Examples.NaiveListener
public import Minimemo.Examples.PragmaticListener
public import Minimemo.Examples.Knows
public import Minimemo.Examples.Notation
public import Minimemo.Theory.Transfer
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The examples with real numbers

This file proves that the example models return, with real numbers, the arrays that they return
with rational numbers.

Lean evaluates the model with rational numbers. The interpretations of the model with rational and
with real numbers are compatible along the inclusion of the rational numbers: the denotation
agrees on rational numbers. So the array with real numbers is the image of the array with rational
numbers.

## Main results

* `Memo.NaiveListener.compat`: the two interpretations are compatible.
* `Memo.NaiveListener.rows_real`, `Memo.PragmaticListener.rows_real`, `Memo.Knows.rows_speakerKnows_real`
  and the others: the arrays of the example models with real numbers.
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

/-- A model with the interpretation of the naive listener has, with real numbers, the image of
its array with rational numbers. -/
theorem rows_real_of {N : Type} [DecidableEq N] {M : Model Agent N Dom Fn}
    {rows : List (List ℚ)} (h : Model.rows interp M = some rows) :
    Model.rows (interpOf ℝ) M = some (rows.map (List.map (↑))) := by
  rw [Model.rows_map Rat.cast_strictMono compat, h]
  rfl

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
  rw [rows_real_of hq]
  norm_num

/-- The model in which the speaker chooses the utterance first returns the same array as the naive
listener, with real numbers. -/
theorem rows_utteranceFirst_real :
    Model.rows (interpOf ℝ) utteranceFirst = Model.rows (interpOf ℝ) model := by
  rw [Model.rows_map Rat.cast_strictMono compat, Model.rows_map Rat.cast_strictMono compat,
    rows_utteranceFirst]

/-- The listener whose speaker chooses the utterance first is equivalent to the naive listener,
whose speaker chooses the referent first. -/
theorem equiv_utteranceFirst : Model.Equiv (interpOf ℝ) utteranceFirst model :=
  Model.equiv_of_rows_eq rows_utteranceFirst_real

end Memo.NaiveListener

namespace Memo.Knows

open NaiveListener (interpOf rows_real_of)

/-- The models with `knows` return the same arrays with real numbers. -/
theorem rows_speakerKnows_real :
    Model.rows (interpOf ℝ) speakerKnows =
      some [[1/2, 1/2, 0], [0, 0, 1/2], [1/2, 0, 0], [0, 1/2, 1/2]] := by
  rw [rows_real_of rows_speakerKnows]
  norm_num

theorem rows_nestedKnows_real :
    Model.rows (interpOf ℝ) nestedKnows =
      some [[1/2, 1/2, 0], [0, 0, 1/2], [1/2, 0, 0], [0, 1/2, 1/2]] := by
  rw [rows_real_of rows_nestedKnows]
  norm_num

theorem rows_knowsOther_real :
    Model.rows (interpOf ℝ) knowsOther =
      some [[1/3, 1/3, 1/3], [1/6, 1/6, 1/6], [1/6, 1/6, 1/6], [1/3, 1/3, 1/3]] := by
  rw [rows_real_of rows_knowsOther]
  norm_num

end Memo.Knows

namespace Memo.NotationExample

/-- The naive listener written in the syntax of memo returns the same array with real numbers. -/
theorem rows_naive_real :
    Model.rows (NaiveListener.interpOf ℝ) naive =
      some [[1/2, 1/2, 0], [0, 0, 1], [1, 0, 0], [0, 1/2, 1/2]] := by
  rw [NaiveListener.rows_real_of rows_naive]
  norm_num

end Memo.NotationExample

namespace Memo.PragmaticListener

open NaiveListener (denotesOf_cast countOf_cast domOf)

theorem naiveOf_cast (a b : ℚ) : naiveOf (a : ℝ) (b : ℝ) = ((naiveOf a b : ℚ) : ℝ) := by
  simp only [naiveOf, denotesOf_cast, countOf_cast, Rat.cast_div]

/-- The interpretations of the pragmatic listener with rational and with real numbers are
compatible. -/
theorem compat : Interp.Compat (Rat.castHom ℝ) (interpOf ℚ) (interpOf ℝ) :=
  Interp.compat_ofField Rat.cast_strictMono (fun d ↦ by cases d <;> rfl)
    (fun d j ↦ by cases d <;> simp [domOf]) fun f x ↦ by
      cases f
      exact naiveOf_cast _ _

/-- The pragmatic listener with real numbers: at *green* it gives the green circle the probability
3/5 and the green square 2/5. -/
theorem rows_real :
    Model.rows (interpOf ℝ) model =
      some [[2/5, 3/5, 0],
            [0,   0,   1],
            [1,   0,   0],
            [0,   3/5, 2/5]] := by
  have hq : Model.rows interp model =
      some [[2/5, 3/5, 0], [0, 0, 1], [1, 0, 0], [0, 3/5, 2/5]] := by decide +kernel
  rw [Model.rows_map Rat.cast_strictMono compat, hq]
  norm_num

end Memo.PragmaticListener
