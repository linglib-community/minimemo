/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import MinimemoTheory.Table.Get
public import MinimemoTheory.Factor
public import Mathlib.Tactic.SplitIfs

/-!
# Tables as factors

This file proves that the operations on stored tables compute the operations on factors.

An assignment of a position below its size to every variable is a choice of a value for every
choice, so a table gives a factor, `Memo.Table.toFactor`. The table that combines tables with an
operator gives the operator applied to their factors, and the sum of a table over a list of
variables gives the sum of its factor over those choices.

## Main definitions

* `Memo.Table.toFactor size t`: the factor of the table `t`.

## Main results

* `Memo.Table.get_op`, `Memo.Table.get_sumOut`, `Memo.Table.get_rename`: the numbers of the tables
  that the operations build.
* `Memo.Table.toFactor_op`: the factor of a combination of tables.
* `Memo.Table.toFactor_sumOver`: the factor of a sum over a list of variables.
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

section Factor

variable [Semifield K]

/-- The **factor of a table**: its number at each assignment of a position below its size to every
variable. -/
def toFactor (size : ℕ → ℕ) (t : Table K) : Factor (fun i ↦ Fin (size i)) K :=
  fun σ ↦ t.get size fun i ↦ σ i

/-- The factor of the table that combines tables with `f` is `f` at their factors. -/
theorem toFactor_op {k : ℕ} (f : (Fin k → K) → K) (ts : Fin k → Table K)
    (σ : ∀ i, Fin (size i)) :
    toFactor size (op size f ts) σ = f fun i ↦ toFactor size (ts i) σ :=
  get_op f ts fun i ↦ (σ i).isLt

/-- The factor of the sum of a table over a variable is the sum of its factor over that choice. -/
theorem toFactor_sumOut (i : ℕ) (t : Table K) :
    toFactor size (t.sumOut size i) = (toFactor size t).sumOver {i} := by
  funext σ
  simp only [toFactor, Factor.sumOver]
  rw [get_sumOut i t fun k ↦ (σ k).isLt,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ t.get size (Function.update (fun k ↦ (σ k : ℕ)) i j))
      (size i)]
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

/-- The factor of the sum of a table over a list of distinct variables is the sum of its factor
over those choices. -/
theorem toFactor_sumOver (I : List ℕ) (hI : I.Nodup) (t : Table K) :
    toFactor size (t.sumOver size I) = (toFactor size t).sumOver I.toFinset := by
  induction I generalizing t with
  | nil => simp [Table.sumOver]
  | cons i I ih =>
    have hd : Disjoint I.toFinset {i} := by simpa using (List.nodup_cons.1 hI).1
    have h := ih (List.nodup_cons.1 hI).2 (t.sumOut size i)
    rw [toFactor_sumOut, ← Factor.sumOver_union hd] at h
    rw [List.toFinset_cons, Finset.insert_eq, Finset.union_comm]
    exact h

/-- The factor of a table does not depend on a choice that is not a variable of the table. -/
theorem toFactor_updateFinset_singleton {t : Table K} {i : ℕ} (hi : i ∉ t.vars)
    (σ : ∀ i, Fin (size i)) (τ : ∀ j : ({i} : Finset ℕ), Fin (size j)) :
    toFactor size t (Function.updateFinset σ {i} τ) = toFactor size t σ := by
  refine t.get_congr fun v hv ↦ ?_
  have hne : v ≠ i := fun h ↦ hi (h ▸ hv)
  simp [Function.updateFinset, hne]

end Factor

end Memo.Table
