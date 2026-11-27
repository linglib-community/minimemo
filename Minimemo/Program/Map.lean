/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program.Basic
public import Minimemo.Table.Map

/-!
# Programs over two kinds of numbers

This file proves that a program gives the same array over two fields of numbers, when one field
embeds in the other and the operators of the program agree.

Two programs are related along a map `φ` of numbers if they have the same steps and terms, the
numbers of the second are the images of the numbers of the first, and each operator of the second
has, at the images of some numbers, the image of what the operator of the first has at those
numbers. If `φ` is a homomorphism of fields that preserves the order, the tables of the second
program are the images of the tables of the first.

So a model with rational numbers, which Lean can evaluate, gives the array of the same model with
real numbers.

## Main definitions

* `Memo.Term.Rel φ t t'`, `Memo.Step.Rel φ s s'`, `Memo.Program.Rel φ p p'`: the relation.

## Main results

* `Memo.Term.Rel.eval`, `Memo.Step.Rel.table`: the tables of related terms and steps.
* `Memo.Program.Rel.entries`, `Memo.Program.Rel.rows`: the arrays of related programs.
-/

@[expose] public section

universe u

namespace Memo

variable {K L : Type u}

mutual

/-- Two terms are **related** along `φ` if they have the same form, the numbers of the second are
the images of those of the first, and its operators agree with those of the first along `φ`. -/
inductive Term.Rel (φ : K → L) : Term K → Term L → Prop
  | lit {r : K} {r' : L} (h : r' = φ r) : Term.Rel φ (.lit r) (.lit r')
  | op {k : ℕ} {f : (Fin k → K) → K} {f' : (Fin k → L) → L} {ts : Fin k → Term K}
      {ts' : Fin k → Term L} (hf : ∀ x, f' (fun i ↦ φ (x i)) = φ (f x))
      (h : ∀ i, Term.Rel φ (ts i) (ts' i)) : Term.Rel φ (.op f ts) (.op f' ts')
  | val (i : ℕ) {v : ℕ → K} {v' : ℕ → L} (hv : ∀ j, v' j = φ (v j)) :
      Term.Rel φ (.val i v) (.val i v')
  | expect (w : ℕ) (over : List ℕ) {t : Term K} {t' : Term L} (h : Term.Rel φ t t') :
      Term.Rel φ (.expect w over t) (.expect w over t')
  | rename (links : List (ℕ × ℕ)) {t : Term K} {t' : Term L} (h : Term.Rel φ t t') :
      Term.Rel φ (.rename links t) (.rename links t')
  | best (i : ℕ) {t : Term K} {t' : Term L} (h : Term.Rel φ t t') :
      Term.Rel φ (.best i t) (.best i t')
  | after {s : Step K} {s' : Step L} {t : Term K} {t' : Term L} (hs : Step.Rel φ s s')
      (h : Term.Rel φ t t') : Term.Rel φ (.after s t) (.after s' t')

/-- Two steps are **related** along `φ` if they have the same form and related terms. -/
inductive Step.Rel (φ : K → L) : Step K → Step L → Prop
  | chooses (w : ℕ) (over : List ℕ) {t : Term K} {t' : Term L} (h : Term.Rel φ t t') :
      Step.Rel φ (.chooses w over t) (.chooses w over t')
  | weighs (w : ℕ) {t : Term K} {t' : Term L} (h : Term.Rel φ t t') :
      Step.Rel φ (.weighs w t) (.weighs w t')
  | observes (w : ℕ) (over : List ℕ) : Step.Rel φ (.observes w over) (.observes w over)
  | forgets (w : ℕ) (over : List ℕ) : Step.Rel φ (.forgets w over) (.forgets w over)

end

/-- Two programs are **related** along `φ` if they have the same sizes and axes, and related steps
and terms. -/
structure Program.Rel (φ : K → L) (p : Program K) (p' : Program L) : Prop where
  sizes : p'.sizes = p.sizes
  axes : p'.axes = p.axes
  steps : List.Forall₂ (Step.Rel φ) p.steps p'.steps
  ret : Term.Rel φ p.ret p'.ret

variable [Semifield K] [LinearOrder K] [Semifield L] [LinearOrder L] {size : ℕ → ℕ}

theorem Term.eval_op {k : ℕ} (f : (Fin k → K) → K) (ts : Fin k → Term K) (W : Array (Table K)) :
    (Term.op f ts).eval size W = Table.op f fun i ↦ (ts i).eval size W := by
  rw [Term.eval]
  congr 1
  funext i
  simp

variable (φ : K →+* L)

omit [LinearOrder K] [LinearOrder L] in
theorem getD_map_tables (W : Array (Table K)) (w : ℕ) :
    (W.map (Table.map φ)).getD w (.const 1) = (W.getD w (.const 1)).map φ :=
  Table.getD_map (Table.map φ) (by rw [Table.map_const, map_one]) W w

variable {φ} (hφ : StrictMono φ)
include hφ

set_option linter.unusedSectionVars false in
mutual

/-- The table of a term is the image of the table of a related term. -/
theorem Term.Rel.eval : ∀ {t : Term K} {t' : Term L}, Term.Rel φ t t' → ∀ W : Array (Table K),
    t'.eval size (W.map (Table.map φ)) = (t.eval size W).map φ
  | _, _, .lit h, W => by rw [Term.eval, Term.eval, Table.map_const, h]
  | _, _, .op hf h, W => by
    rw [Term.eval_op, Term.eval_op, ← Table.map_op (map_zero φ) hf]
    congr 1
    funext i
    exact Term.Rel.eval (h i) W
  | _, _, .val i hv, W => by
    rw [Term.eval, Term.eval, Table.map_ofFn]
    simp only [hv]
  | _, _, .expect w over h, W => by
    rw [Term.eval, Term.eval, Term.Rel.eval h W, getD_map_tables, Table.map_mul,
      Table.map_sumOver (map_zero φ) (map_add φ)]
  | _, _, .rename links h, W => by
    rw [Term.eval, Term.eval, Term.Rel.eval h W, Table.map_rename (map_zero φ)]
  | _, _, .best i h, W => by
    rw [Term.eval, Term.eval, Term.Rel.eval h W, Table.map_best φ hφ]
  | _, _, .after hs h, W => by
    rw [Term.eval, Term.eval, Step.Rel.table hs W, ← Array.map_push]
    exact Term.Rel.eval h _

/-- The table of a step is the image of the table of a related step. -/
theorem Step.Rel.table : ∀ {s : Step K} {s' : Step L}, Step.Rel φ s s' → ∀ W : Array (Table K),
    s'.table size (W.map (Table.map φ)) = (s.table size W).map φ
  | _, _, .chooses w over h, W => by
    simp only [Step.table]
    rw [Term.Rel.eval h W, getD_map_tables, Table.map_sumOver (map_zero φ) (map_add φ),
      Table.map_div, Table.map_mul]
  | _, _, .weighs w h, W => by
    simp only [Step.table]
    rw [Term.Rel.eval h W, getD_map_tables, Table.map_mul]
  | _, _, .observes w over, W => by
    simp only [Step.table]
    rw [getD_map_tables, Table.map_sumOver (map_zero φ) (map_add φ), Table.map_div]
  | _, _, .forgets w over, W => by
    simp only [Step.table]
    rw [getD_map_tables, Table.map_sumOver (map_zero φ) (map_add φ)]

end

theorem foldl_run_map : ∀ {l : List (Step K)} {l' : List (Step L)},
    List.Forall₂ (Step.Rel φ) l l' → ∀ W : Array (Table K),
      l'.foldl (Step.run size) (W.map (Table.map φ)) =
        (l.foldl (Step.run size) W).map (Table.map φ)
  | _, _, .nil, _ => rfl
  | _, _, .cons hs hl, W => by
    rw [List.foldl_cons, List.foldl_cons, Step.run, Step.Rel.table hφ hs W, ← Array.map_push]
    exact foldl_run_map hl _

variable {p : Program K} {p' : Program L}

/-- The table that a program returns is the image of the table of a related program. -/
theorem Program.Rel.table (h : Program.Rel φ p p') : p'.table = p.table.map φ := by
  have hsize : p'.size = p.size := by funext i; rw [Program.size, Program.size, h.sizes]
  rw [Program.table, Program.table, hsize]
  have h1 : (#[Table.const 1] : Array (Table L)) = (#[Table.const 1] : Array (Table K)).map
      (Table.map φ) := by simp [Table.map_const]
  rw [h1, foldl_run_map hφ h.steps, Term.Rel.eval hφ h.ret]

/-- The entries of the array of a program are the images of the entries of a related program. -/
theorem Program.Rel.entries (h : Program.Rel φ p p') : p'.entries = p.entries.map φ := by
  have hsize : p'.size = p.size := by funext i; rw [Program.size, Program.size, h.sizes]
  simp only [Program.entries, h.table hφ, hsize, h.axes, Table.get_map (map_zero φ)]
  rw [← Table.map_ofFn]
  simp [Table.map]

/-- The rows of the array of a program are the images of the rows of a related program. -/
theorem Program.Rel.rows (h : Program.Rel φ p p') : p'.rows = p.rows.map (List.map φ) := by
  have hsize : p'.size = p.size := by funext i; rw [Program.size, Program.size, h.sizes]
  simp only [Program.rows, h.table hφ, hsize, h.axes, Table.get_map (map_zero φ)]
  cases (withSizes p.size p.axes).getLast? <;> simp

end Memo
