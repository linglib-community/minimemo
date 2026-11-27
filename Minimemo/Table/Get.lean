/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Table.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Tactic.Ring

/-!
# Reading a stored table

This file proves that a table built from a function has the values of that function.

A table stores its numbers in row-major order, and reads the number at an assignment from the
place `Memo.Table.index`. The place of a list of positions among all the lists of positions is the
number with those digits, in the mixed radix of the sizes.

## Main results

* `Memo.Table.getElem?_positions`: the list of positions at the place of `js` is `js`.
* `Memo.Table.get_ofFn`: the table of a function has the value of the function at every
  assignment that is in range, if the function depends on the variables of the table only.
-/

@[expose] public section

namespace Memo.Table

variable {K : Type*}

/-- The place of a list of positions among the lists of positions for the given sizes. -/
def place : List ℕ → List ℕ → ℕ
  | _ :: ms, j :: js => j * ms.prod + place ms js
  | _, _ => 0

theorem length_positions (ms : List ℕ) : (positions ms).length = ms.prod := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [positions, List.length_flatMap, List.length_map, ih, List.prod_cons]
    simp

theorem length_flatMap_range {α : Type*} (g : ℕ → List α) (L : ℕ) (hg : ∀ k, (g k).length = L)
    (m : ℕ) : ((List.range m).flatMap g).length = m * L := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, List.flatMap_append, ih, hg, Nat.succ_mul]

theorem getElem?_flatMap_range {α : Type*} (g : ℕ → List α) (L : ℕ)
    (hg : ∀ k, (g k).length = L) {m j e : ℕ} (hj : j < m) (he : e < L) :
    ((List.range m).flatMap g)[j * L + e]? = (g j)[e]? := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append]
    have hlen := length_flatMap_range g L hg m
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left, ih h]
      rw [hlen]
      calc j * L + e < j * L + L := by omega
        _ = (j + 1) * L := by ring
        _ ≤ m * L := Nat.mul_le_mul_right L h
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp

theorem place_lt {js ms : List ℕ} (h : List.Forall₂ (· < ·) js ms) : place ms js < ms.prod := by
  induction h with
  | nil => simp [place]
  | @cons j m js ms hjm _ ih =>
    rw [place, List.prod_cons]
    calc j * ms.prod + place ms js < j * ms.prod + ms.prod := by omega
      _ = (j + 1) * ms.prod := by ring
      _ ≤ m * ms.prod := Nat.mul_le_mul_right _ hjm

/-- The list of positions at the place of `js` is `js`. -/
theorem getElem?_positions {js ms : List ℕ} (h : List.Forall₂ (· < ·) js ms) :
    (positions ms)[place ms js]? = some js := by
  induction h with
  | nil => rfl
  | @cons j m js ms hjm h ih =>
    rw [positions, place, getElem?_flatMap_range _ ms.prod
      (fun k ↦ by rw [List.length_map, length_positions]) hjm (place_lt h), List.getElem?_map, ih]
    rfl

theorem foldl_index (σ : ℕ → ℕ) (vars : List (ℕ × ℕ)) (a : ℕ) :
    vars.foldl (fun at' v ↦ at' * v.2 + σ v.1) a =
      a * (vars.map (·.2)).prod + place (vars.map (·.2)) (vars.map fun v ↦ σ v.1) := by
  induction vars generalizing a with
  | nil => simp [place]
  | cons v vars ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.prod_cons, place]
    ring

theorem index_eq_place (vars : List (ℕ × ℕ)) (σ : ℕ → ℕ) :
    index vars σ = place (vars.map (·.2)) (vars.map fun v ↦ σ v.1) := by
  rw [index, foldl_index, zero_mul, zero_add]

theorem assign_map (vars : List (ℕ × ℕ)) (σ : ℕ → ℕ) (i : ℕ) :
    assign vars (vars.map fun v ↦ σ v.1) i = if i ∈ vars.map (·.1) then σ i else 0 := by
  unfold assign
  induction vars with
  | nil => simp
  | cons v vars ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons, List.mem_cons]
    by_cases h : i = v.1
    · simp [h]
    · have hb : (i == v.1) = false := beq_false_of_ne h
      simp only [hb, h, false_or]
      exact ih

/-- The table of a function has, at an assignment that is in range, the value of the function at
the assignment that agrees with it on the variables of the table and is zero elsewhere. -/
theorem get_ofFn_assign [Zero K] (vars : List (ℕ × ℕ)) (f : (ℕ → ℕ) → K) {σ : ℕ → ℕ}
    (hσ : ∀ v ∈ vars, σ v.1 < v.2) :
    (ofFn vars f).get σ = f (assign vars (vars.map fun v ↦ σ v.1)) := by
  have h : List.Forall₂ (· < ·) (vars.map fun v ↦ σ v.1) (vars.map (·.2)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact hσ
  simp [get, ofFn, index_eq_place, getElem?_positions h]

/-- The table of a function has the value of the function at every assignment that is in range,
if the function depends on the variables of the table only. -/
theorem get_ofFn [Zero K] (vars : List (ℕ × ℕ)) (f : (ℕ → ℕ) → K) {σ : ℕ → ℕ}
    (hσ : ∀ v ∈ vars, σ v.1 < v.2)
    (hf : ∀ σ σ' : ℕ → ℕ, (∀ v ∈ vars, σ v.1 = σ' v.1) → f σ = f σ') :
    (ofFn vars f).get σ = f σ := by
  rw [get_ofFn_assign vars f hσ]
  refine hf _ _ fun v hv ↦ ?_
  have hmem : v.1 ∈ vars.map (·.1) := List.mem_map_of_mem hv
  simp only [assign_map, hmem, ite_true]

end Memo.Table
