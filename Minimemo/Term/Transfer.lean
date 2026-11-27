/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Term.Basic
public import Minimemo.Table.Map

/-!
# A program in two fields of numbers

This file proves that a program has the same array in two fields of numbers, when one embeds in
the other.

A program has no numbers of its own. Two interpretations are compatible along a map `φ` of numbers
if their domains have the same sizes, and the values, the operators and the literals of the second
are the images of those of the first. If `φ` is a homomorphism of fields that preserves the order,
the tables of every program in the second interpretation are the images of its tables in the
first. The interpretations of the operators of memo in two ordered fields are compatible.

So an array that Lean computes with rational numbers is the array of the same model with real
numbers.

## Main results

* `Memo.Term.eval_map`: the table of a term.
* `Memo.Program.entries_map`, `Memo.Program.rows_map`: the array of a program.
-/

@[expose] public section

universe u

namespace Memo

variable {D : Type u} {F : ℕ → Type u} {K L : Type u}

section Eval

variable [Semifield K] [LinearOrder K] [Semifield L] [LinearOrder L] {size : ℕ → ℕ}
  {I : Interp D F K} {J : Interp D F L}

theorem Term.eval_op {k : ℕ} (o : Prim k ⊕ F k) (ts : Fin k → Term D F) (W : Array (Table K)) :
    (Term.op o ts).eval I size W = Table.op size (I.op o) fun i ↦ (ts i).eval I size W := by
  rw [Term.eval]
  congr 1
  funext i
  simp

omit [LinearOrder K] [LinearOrder L] in
theorem getD_map_tables (φ : K →+* L) (W : Array (Table K)) (w : ℕ) :
    (W.map (Table.map φ)).getD w (.const 1) = (W.getD w (.const 1)).map φ :=
  Table.getD_map (Table.map φ) (by rw [Table.map_const, map_one]) W w

variable {φ : K →+* L} (hφ : StrictMono φ) (h : Interp.Compat φ I J)
include hφ h

/-- The table of a term in the second interpretation is the image of its table in the first. -/
theorem Term.eval_map : ∀ (t : Term D F) (W : Array (Table K)),
    t.eval J size (W.map (Table.map φ)) = (t.eval I size W).map φ
  | .lit q, W => by rw [Term.eval, Term.eval, Table.map_const, h.lit]
  | .op o ts, W => by
    rw [Term.eval_op, Term.eval_op, ← Table.map_op (map_zero φ) (h.op o)]
    congr 1
    funext i
    exact Term.eval_map (ts i) W
  | .val i d, W => by
    rw [Term.eval, Term.eval, Table.map_ofFn]
    simp only [h.val]
  | .ref w, W => by rw [Term.eval, Term.eval, getD_map_tables]
  | .sum over t, W => by
    rw [Term.eval, Term.eval, Term.eval_map t W, Table.map_sumOver (map_zero φ) (map_add φ)]
  | .rename links t, W => by
    rw [Term.eval, Term.eval, Term.eval_map t W, Table.map_rename (map_zero φ)]
  | .best i t, W => by
    rw [Term.eval, Term.eval, Term.eval_map t W, Table.map_best φ hφ]
  | .letE t₁ t₂, W => by
    rw [Term.eval, Term.eval, Term.eval_map t₁ W, ← Array.map_push]
    exact Term.eval_map t₂ _

omit hφ [LinearOrder K] [LinearOrder L] in
theorem Program.size_map (p : Program D F) : p.size J = p.size I := by
  funext i
  simp only [Program.size]
  cases p.doms[i]? <;> simp [h.size]

/-- The table that a program returns in the second interpretation is the image of its table in the
first. -/
theorem Program.table_map (p : Program D F) : p.table J = (p.table I).map φ := by
  rw [Program.table, Program.table, p.size_map h]
  have h1 : (#[Table.const 1] : Array (Table L)) = (#[Table.const 1] : Array (Table K)).map
      (Table.map φ) := by simp [Table.map_const]
  rw [h1, Term.eval_map hφ h]

/-- The entries of the array of a program in the second interpretation are the images of its
entries in the first. -/
theorem Program.entries_map (p : Program D F) : p.entries J = (p.entries I).map φ := by
  simp only [Program.entries, p.table_map hφ h, p.size_map h, Table.get_map (map_zero φ)]
  rw [← Table.map_ofFn]
  simp [Table.map]

/-- The rows of the array of a program in the second interpretation are the images of its rows in
the first. -/
theorem Program.rows_map (p : Program D F) : p.rows J = (p.rows I).map (List.map φ) := by
  simp only [Program.rows, p.table_map hφ h, p.size_map h, Table.get_map (map_zero φ)]
  cases p.axes.getLast? <;> simp

end Eval

end Memo
