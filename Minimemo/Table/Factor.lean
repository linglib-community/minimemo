/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Table.Get
public import Minimemo.Belief.Basic
public import Mathlib.Tactic.SplitIfs

/-!
# Tables as factors

This file proves that the operations on stored tables compute the operations on factors.

Fix a size for every variable. A table is sized if each of its variables has that size. An
assignment of a position below its size to every variable is a choice of a value for every choice,
so a table gives a factor, `Memo.Table.toFactor`. The product and the quotient of sized tables give
the product and the quotient of their factors, and the sum of a sized table over a list of
variables gives the sum of its factor over those choices.

## Main definitions

* `Memo.Table.Sized size t`: each variable of the table `t` has the size that `size` gives it.
* `Memo.Table.toFactor size t`: the factor of the table `t`.

## Main results

* `Memo.Table.toFactor_mul`, `Memo.Table.toFactor_div`: the factor of a product or a quotient.
* `Memo.Table.toFactor_sumOver`: the factor of a sum over a list of variables.
-/

@[expose] public section

namespace Memo.Table

variable {K : Type*} {size : ℕ → ℕ}

/-- A table is **sized** if each of its variables has the size that `size` gives it. -/
def Sized (size : ℕ → ℕ) (t : Table K) : Prop := ∀ v ∈ t.vars, v.2 = size v.1

theorem index_congr {vars : List (ℕ × ℕ)} {σ σ' : ℕ → ℕ} (h : ∀ v ∈ vars, σ v.1 = σ' v.1) :
    index vars σ = index vars σ' := by
  rw [index_eq_place, index_eq_place, List.map_congr_left h]

/-- A table has the same number at two assignments that agree on its variables. -/
theorem get_congr [Zero K] (t : Table K) {σ σ' : ℕ → ℕ} (h : ∀ v ∈ t.vars, σ v.1 = σ' v.1) :
    t.get σ = t.get σ' := by
  rw [get, get, index_congr h]

theorem mem_insertVar {v w : ℕ × ℕ} {l : List (ℕ × ℕ)} (h : w ∈ insertVar v l) :
    w = v ∨ w ∈ l := by
  induction l with
  | nil => simpa [insertVar] using h
  | cons u us ih =>
    simp only [insertVar] at h
    split_ifs at h
    · simpa using h
    · exact .inr h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr List.mem_cons_self
      · exact (ih h).imp id (List.mem_cons_of_mem _)

theorem key_mem_insertVar {v : ℕ × ℕ} {l : List (ℕ × ℕ)} {k : ℕ}
    (h : k = v.1 ∨ k ∈ l.map (·.1)) : k ∈ (insertVar v l).map (·.1) := by
  induction l with
  | nil => simpa [insertVar] using h
  | cons u us ih =>
    simp only [insertVar]
    simp only [List.map_cons, List.mem_cons] at h
    split_ifs with h₁ h₂
    · simpa using h
    · rcases h with rfl | h
      · simp [h₂]
      · simpa using h
    · rcases h with rfl | rfl | h
      · exact List.mem_cons_of_mem _ (ih (.inl rfl))
      · simp
      · exact List.mem_cons_of_mem _ (ih (.inr h))

theorem mem_distinct {xs : List (ℕ × ℕ)} {w : ℕ × ℕ} (h : w ∈ distinct xs) : w ∈ xs := by
  induction xs with
  | nil => simp [distinct] at h
  | cons x xs ih =>
    rcases mem_insertVar (v := x) (l := distinct xs) h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem key_mem_distinct {xs : List (ℕ × ℕ)} {k : ℕ} (h : k ∈ xs.map (·.1)) :
    k ∈ (distinct xs).map (·.1) := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    refine key_mem_insertVar (v := x) (l := distinct xs) ?_
    rcases List.mem_cons.1 h with h | h
    · exact .inl h
    · exact .inr (ih h)

/-- Two assignments that agree on the variables of `distinct xs` agree on those of `xs`. -/
theorem agree_of_distinct {xs : List (ℕ × ℕ)} {σ σ' : ℕ → ℕ}
    (h : ∀ v ∈ distinct xs, σ v.1 = σ' v.1) : ∀ w ∈ xs, σ w.1 = σ' w.1 := fun w hw ↦ by
  obtain ⟨v, hv, hvw⟩ := List.mem_map.1 (key_mem_distinct (List.mem_map_of_mem (f := (·.1)) hw))
  have := h v hv
  rwa [hvw] at this

theorem sized_ofFn (vars : List (ℕ × ℕ)) (f : (ℕ → ℕ) → K) :
    (ofFn vars f).Sized size ↔ ∀ v ∈ vars, v.2 = size v.1 := Iff.rfl

theorem sized_const (k : K) : (const k).Sized size := fun _ h ↦ by simp [const] at h

section Map₂

variable [Zero K] {s t : Table K} {σ : ℕ → ℕ}

theorem Sized.map₂ (g : K → K → K) (hs : s.Sized size) (ht : t.Sized size) :
    (map₂ g s t).Sized size := fun v hv ↦
  (List.mem_append.1 (mem_distinct hv)).elim (hs v) (ht v)

/-- The table that combines two sized tables with `g` has, at an assignment in range, the value
of `g` at their numbers. -/
theorem get_map₂ (g : K → K → K) (hs : s.Sized size) (ht : t.Sized size)
    (hσ : ∀ i, σ i < size i) : (map₂ g s t).get σ = g (s.get σ) (t.get σ) := by
  refine get_ofFn _ _ (fun v hv ↦ ?_) fun σ₁ σ₂ h ↦ ?_
  · rw [Sized.map₂ g hs ht v hv]
    exact hσ _
  · have h' := agree_of_distinct h
    rw [s.get_congr fun w hw ↦ h' w (List.mem_append_left _ hw),
      t.get_congr fun w hw ↦ h' w (List.mem_append_right _ hw)]

end Map₂

section Sum

variable [AddCommMonoid K] {t : Table K} {σ : ℕ → ℕ}

theorem foldl_add_range (g : ℕ → K) (n : ℕ) :
    (List.range n).foldl (fun total j ↦ total + g j) 0 = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

theorem Sized.sumOut (i : ℕ) (ht : t.Sized size) : (t.sumOut i).Sized size := by
  unfold Table.sumOut
  cases t.vars.find? (·.1 == i) with
  | none => exact ht
  | some v => exact fun w hw ↦ ht w (List.mem_of_mem_filter hw)

/-- The sum of a sized table over one of its variables has, at an assignment in range, the sum of
the numbers of the table over the positions of that variable. -/
theorem get_sumOut {i : ℕ} (hi : i ∈ t.vars.map (·.1)) (ht : t.Sized size)
    (hσ : ∀ i, σ i < size i) :
    (t.sumOut i).get σ = ∑ j ∈ Finset.range (size i), t.get (Function.update σ i j) := by
  unfold Table.sumOut
  cases h : t.vars.find? (·.1 == i) with
  | none =>
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hi
    simpa using List.find?_eq_none.1 h v hv
  | some v =>
    have hv : v ∈ t.vars := List.mem_of_find?_eq_some h
    have hvi : v.1 = i := by simpa using List.find?_some h
    simp only
    rw [get_ofFn _ _ (fun w hw ↦ by rw [ht w (List.mem_of_mem_filter hw)]; exact hσ _),
      foldl_add_range, ht v hv, hvi]
    intro σ₁ σ₂ hagree
    congr 1
    funext total j
    congr 1
    refine t.get_congr fun w hw ↦ ?_
    by_cases hw' : w.1 = i
    · simp [hw']
    · simpa [Function.update, hw'] using hagree w (List.mem_filter.2 ⟨hw, by simpa using hw'⟩)

theorem getD_map_zero {α : Type*} [Zero α] (h : α → α) (h0 : h 0 = 0) (a : Array α) (k : ℕ) :
    (a.map h).getD k 0 = h (a.getD k 0) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[k]? <;> simp [h0]

theorem Sized.sumOver_singleton (v : ℕ × ℕ) (ht : t.Sized size) :
    (t.sumOver [v]).Sized size := by
  simp only [Table.sumOver, List.foldl_cons, List.foldl_nil]
  split_ifs
  · exact ht.sumOut _
  · exact ht

/-- The sum of a sized table over a variable has, at an assignment in range, the sum of the
numbers of the table over the positions of that variable, whether or not the table has it. -/
theorem get_sumOver_singleton (i : ℕ) (ht : t.Sized size) (hσ : ∀ i, σ i < size i) :
    (t.sumOver [(i, size i)]).get σ =
      ∑ j ∈ Finset.range (size i), t.get (Function.update σ i j) := by
  simp only [Table.sumOver, List.foldl_cons, List.foldl_nil]
  split_ifs with h
  · refine get_sumOut ?_ ht hσ
    obtain ⟨v, hv, hvi⟩ := List.any_eq_true.1 h
    exact List.mem_map.2 ⟨v, hv, by simpa using hvi⟩
  · have hi : ∀ w ∈ t.vars, w.1 ≠ i := fun w hw hwi ↦
      h (List.any_eq_true.2 ⟨w, hw, by simpa using hwi⟩)
    have hconst (j : ℕ) : t.get (Function.update σ i j) = t.get σ :=
      t.get_congr fun w hw ↦ by simp [Function.update, hi w hw]
    simp only [hconst]
    rw [Table.get, getD_map_zero _ (by simp), foldl_add_range]
    rfl

end Sum

section Factor

variable [Semifield K] {s t : Table K}

/-- The **factor of a table**: its number at each assignment of a position below its size to every
variable. -/
def toFactor (size : ℕ → ℕ) (t : Table K) : Factor (fun i ↦ Fin (size i)) K :=
  fun σ ↦ t.get fun i ↦ σ i

theorem toFactor_mul (hs : s.Sized size) (ht : t.Sized size) :
    toFactor size (s * t) = toFactor size s * toFactor size t :=
  funext fun σ ↦ get_map₂ _ hs ht fun i ↦ (σ i).isLt

theorem toFactor_div (hs : s.Sized size) (ht : t.Sized size) :
    toFactor size (s / t) = toFactor size s / toFactor size t :=
  funext fun σ ↦ get_map₂ _ hs ht fun i ↦ (σ i).isLt

theorem Sized.mul (hs : s.Sized size) (ht : t.Sized size) : (s * t).Sized size :=
  Sized.map₂ _ hs ht

theorem Sized.div (hs : s.Sized size) (ht : t.Sized size) : (s / t).Sized size :=
  Sized.map₂ _ hs ht

/-- The factor of the sum of a table over a variable is the sum of its factor over that choice. -/
theorem toFactor_sumOver_singleton (i : ℕ) (ht : t.Sized size) :
    toFactor size (t.sumOver [(i, size i)]) = (toFactor size t).sumOver {i} := by
  funext σ
  simp only [toFactor, Factor.sumOver]
  rw [get_sumOver_singleton i ht fun k ↦ (σ k).isLt,
    ← Fin.sum_univ_eq_sum_range (fun j ↦ t.get (Function.update (fun k ↦ (σ k : ℕ)) i j)) (size i)]
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

/-- The factor of a table does not depend on a choice that is not a variable of the table. -/
theorem toFactor_updateFinset_singleton {i : ℕ} (hi : i ∉ t.vars.map (·.1))
    (σ : ∀ i, Fin (size i)) (τ : ∀ j : ({i} : Finset ℕ), Fin (size j)) :
    toFactor size t (Function.updateFinset σ {i} τ) = toFactor size t σ := by
  refine t.get_congr fun v hv ↦ ?_
  have hne : v.1 ≠ i := fun h ↦ hi (h ▸ List.mem_map_of_mem hv)
  simp [Function.updateFinset, hne]

theorem Sized.sumOver (I : List (ℕ × ℕ)) (ht : t.Sized size) : (t.sumOver I).Sized size := by
  induction I generalizing t with
  | nil => exact ht
  | cons v I ih => exact ih (ht.sumOver_singleton v)

/-- The factor of the sum of a table over a list of distinct variables is the sum of its factor
over those choices. -/
theorem toFactor_sumOver (I : List ℕ) (hI : I.Nodup) (ht : t.Sized size) :
    toFactor size (t.sumOver (I.map fun i ↦ (i, size i))) =
      (toFactor size t).sumOver I.toFinset := by
  induction I generalizing t with
  | nil =>
    simp [Table.sumOver]
  | cons i I ih =>
    have hd : Disjoint I.toFinset {i} := by
      simpa using (List.nodup_cons.1 hI).1
    have h := ih (List.nodup_cons.1 hI).2 (ht.sumOver_singleton (i, size i))
    rw [toFactor_sumOver_singleton i ht, ← Factor.sumOver_union hd] at h
    rw [List.toFinset_cons, Finset.insert_eq, Finset.union_comm]
    exact h

end Factor

end Memo.Table
