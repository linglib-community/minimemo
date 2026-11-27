/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program.Basic
public import Minimemo.Table.Map
public import Mathlib.Algebra.Order.Ring.Abs

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

## Main definitions

* `Memo.Interp.Compat φ I J`: the interpretations `I` and `J` are compatible along `φ`.

## Main results

* `Memo.Term.eval_map`, `Memo.Step.table_map`: the tables of a term and of a step.
* `Memo.Program.entries_map`, `Memo.Program.rows_map`: the array of a program.
* `Memo.Interp.compat_ofField`: the interpretations in two ordered fields are compatible.
-/

@[expose] public section

universe u

namespace Memo

variable {D : Type u} {F : ℕ → Type u} {K L : Type u}

/-- Two interpretations are **compatible** along `φ` if their domains have the same sizes, and the
values, the operators and the literals of the second are the images of those of the first. -/
structure Interp.Compat (φ : K → L) (I : Interp D F K) (J : Interp D F L) : Prop where
  size : ∀ d, (J.dom d).size = (I.dom d).size
  val : ∀ d j, (J.dom d).val j = φ ((I.dom d).val j)
  op : ∀ {k : ℕ} (o : Prim k ⊕ F k) (x : Fin k → K), J.op o (fun i ↦ φ (x i)) = φ (I.op o x)
  lit : ∀ q, J.lit q = φ (I.lit q)

section Eval

variable [Semifield K] [LinearOrder K] [Semifield L] [LinearOrder L] {size : ℕ → ℕ}
  {I : Interp D F K} {J : Interp D F L}

theorem Term.eval_op {k : ℕ} (o : Prim k ⊕ F k) (ts : Fin k → Term D F) (W : Array (Table K)) :
    (Term.op o ts).eval I size W = Table.op (I.op o) fun i ↦ (ts i).eval I size W := by
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

set_option linter.unusedSectionVars false in
mutual

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
  | .expect w over t, W => by
    rw [Term.eval, Term.eval, Term.eval_map t W, getD_map_tables, Table.map_mul,
      Table.map_sumOver (map_zero φ) (map_add φ)]
  | .rename links t, W => by
    rw [Term.eval, Term.eval, Term.eval_map t W, Table.map_rename (map_zero φ)]
  | .best i t, W => by
    rw [Term.eval, Term.eval, Term.eval_map t W, Table.map_best φ hφ]
  | .after s t, W => by
    rw [Term.eval, Term.eval, Step.table_map s W, ← Array.map_push]
    exact Term.eval_map t _

/-- The table of a step in the second interpretation is the image of its table in the first. -/
theorem Step.table_map : ∀ (s : Step D F) (W : Array (Table K)),
    s.table J size (W.map (Table.map φ)) = (s.table I size W).map φ
  | .chooses w over t, W => by
    simp only [Step.table]
    rw [Term.eval_map t W, getD_map_tables, Table.map_sumOver (map_zero φ) (map_add φ),
      Table.map_div, Table.map_mul]
  | .weighs w t, W => by
    simp only [Step.table]
    rw [Term.eval_map t W, getD_map_tables, Table.map_mul]
  | .observes w over, W => by
    simp only [Step.table]
    rw [getD_map_tables, Table.map_sumOver (map_zero φ) (map_add φ), Table.map_div]
  | .forgets w over, W => by
    simp only [Step.table]
    rw [getD_map_tables, Table.map_sumOver (map_zero φ) (map_add φ)]

end

theorem foldl_run_map : ∀ (l : List (Step D F)) (W : Array (Table K)),
    l.foldl (Step.run J size) (W.map (Table.map φ)) =
      (l.foldl (Step.run I size) W).map (Table.map φ)
  | [], _ => rfl
  | s :: l, W => by
    rw [List.foldl_cons, List.foldl_cons, Step.run, Step.table_map hφ h s W, ← Array.map_push]
    exact foldl_run_map l _

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
  rw [h1, foldl_run_map hφ h, Term.eval_map hφ h]

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
  cases (withSizes (p.size I) p.axes).getLast? <;> simp

end Eval

/-- The interpretations in two ordered fields are compatible along an embedding that preserves the
order, if the domains and the outside functions are. -/
theorem Interp.compat_ofField [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field L]
    [LinearOrder L] [IsStrictOrderedRing L] {φ : K →+* L} (hφ : StrictMono φ)
    {dom : D → Domain K} {dom' : D → Domain L} {call : {k : ℕ} → F k → (Fin k → K) → K}
    {call' : {k : ℕ} → F k → (Fin k → L) → L} (hsize : ∀ d, (dom' d).size = (dom d).size)
    (hval : ∀ d j, (dom' d).val j = φ ((dom d).val j))
    (hcall : ∀ {k : ℕ} (f : F k) (x : Fin k → K), call' f (fun i ↦ φ (x i)) = φ (call f x)) :
    Interp.Compat φ (.ofField dom call) (.ofField dom' call') where
  size := hsize
  val := hval
  lit q := (map_ratCast φ q).symm
  op o x := by
    rcases o with p | f
    · cases p <;>
        simp [Interp.ofField, Prim.eval, hφ.injective.eq_iff, hφ.lt_iff_lt, hφ.le_iff_le,
          apply_ite φ, abs_eq_max_neg, hφ.monotone.map_max]
    · exact hcall f x

end Memo
