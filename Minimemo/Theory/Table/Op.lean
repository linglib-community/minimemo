/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Theory.Table.Get
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.SplitIfs

/-!
# The numbers of the tables that the operations build

This file proves what number each operation on stored tables puts at an assignment: the table
that combines tables with an operator has the operator applied to their numbers, the table with
variables replaced reads the table at the replaced assignment, and the table summed over a
variable has the sum of the numbers over its positions.

## Main results

* `Memo.Table.get_op`, `Memo.Table.get_rename`, `Memo.Table.get_sumOut`: the numbers of the
  tables that the operations build.
* `Memo.Table.get_congr`: a table has the same number at assignments that agree on its variables.
-/

@[expose] public section

namespace Memo.Table

variable {K : Type*} {size : ℕ → ℕ} {σ : ℕ → ℕ}

theorem index_congr {vars : List ℕ} {σ σ' : ℕ → ℕ} (h : ∀ i ∈ vars, σ i = σ' i) :
    index size vars σ = index size vars σ' := by
  rw [index_eq_place, index_eq_place, List.map_congr_left h]

/-- A table has the same number at two assignments that agree on its variables. -/
theorem get_congr [Zero K] (t : Table K) {σ σ' : ℕ → ℕ} (h : ∀ i ∈ t.vars, σ i = σ' i) :
    t.get size σ = t.get size σ' := by
  rw [get, get, index_congr h]

theorem mem_insertVar {i j : ℕ} {l : List ℕ} : j ∈ insertVar i l ↔ j = i ∨ j ∈ l := by
  induction l with
  | nil => simp [insertVar]
  | cons k ks ih =>
    simp only [insertVar]
    split_ifs with h₁ h₂
    · simp
    · subst h₂
      simp
    · simp only [List.mem_cons, ih]
      tauto

theorem mem_distinct {xs : List ℕ} {j : ℕ} : j ∈ distinct xs ↔ j ∈ xs := by
  induction xs with
  | nil => simp [distinct]
  | cons x xs ih =>
    show j ∈ insertVar x (distinct xs) ↔ _
    rw [mem_insertVar, ih, List.mem_cons]

/-- The table that combines tables with `f` has, at an assignment in range, the value of `f` at
their numbers. -/
theorem get_op [Zero K] {k : ℕ} (f : (Fin k → K) → K) (ts : Fin k → Table K)
    (hσ : ∀ i, σ i < size i) : (op size f ts).get size σ = f fun i ↦ (ts i).get size σ := by
  refine get_ofFn _ _ (fun i _ ↦ hσ i) fun σ₁ σ₂ h ↦ ?_
  congr 1
  funext i
  exact (ts i).get_congr fun v hv ↦
    h v (mem_distinct.2 (List.mem_flatMap.2 ⟨i, List.mem_finRange i, hv⟩))

/-- A renamed table has, at an assignment in range, the number of the table at the assignment read
through the links. -/
theorem get_rename [Zero K] (links : List (ℕ × ℕ)) (t : Table K) (hσ : ∀ i, σ i < size i) :
    (t.rename size links).get size σ = t.get size fun i ↦ σ ((links.lookup i).getD i) := by
  unfold Table.rename
  dsimp only
  split_ifs with h
  · refine t.get_congr fun v hv ↦ ?_
    have := List.all_eq_true.1 h v hv
    rw [beq_iff_eq] at this
    rw [this]
  · refine get_ofFn _ _ (fun i _ ↦ hσ i) fun σ₁ σ₂ hagree ↦ ?_
    exact t.get_congr fun v hv ↦ hagree _ (mem_distinct.2 (List.mem_map_of_mem hv))

theorem rename_nil [Zero K] (t : Table K) : t.rename size [] = t := by
  simp [Table.rename]

theorem getD_map_zero {α : Type*} [Zero α] (h : α → α) (h0 : h 0 = 0) (a : Array α) (k : ℕ) :
    (a.map h).getD k 0 = h (a.getD k 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[k]? <;> simp [h0]

section Sum

variable [AddCommMonoid K]

theorem foldl_add_range (g : ℕ → K) (n : ℕ) :
    (List.range n).foldl (fun total j ↦ total + g j) 0 = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

/-- The sum of a table over a variable has, at an assignment in range, the sum of the numbers of
the table over the positions of that variable, whether or not the table has it. -/
theorem get_sumOut (i : ℕ) (t : Table K) (hσ : ∀ i, σ i < size i) :
    (t.sumOut size i).get size σ =
      ∑ j ∈ Finset.range (size i), t.get size (Function.update σ i j) := by
  unfold Table.sumOut
  split_ifs with hi
  · rw [get_ofFn _ _ (fun i _ ↦ hσ i), foldl_add_range]
    intro σ₁ σ₂ hagree
    congr 1
    funext total j
    congr 1
    refine t.get_congr fun v hv ↦ ?_
    by_cases hv' : v = i
    · simp [hv']
    · simpa [Function.update, hv'] using hagree v (List.mem_filter.2 ⟨hv, by simpa using hv'⟩)
  · have hconst (j : ℕ) : t.get size (Function.update σ i j) = t.get size σ :=
      t.get_congr fun v hv ↦ by
        have : v ≠ i := fun h ↦ hi (h ▸ hv)
        simp [Function.update, this]
    simp only [hconst]
    rw [Table.get, getD_map_zero _ (by simp), foldl_add_range]
    rfl

end Sum

end Memo.Table
