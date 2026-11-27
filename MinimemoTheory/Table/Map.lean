/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Table
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# The image of a table

This file defines the image of a table under a map of numbers and proves that the operations on
tables commute with a homomorphism of fields that preserves the order.

A model with rational numbers can be evaluated. These results carry its tables to the tables of
the same model with real numbers.

## Main definitions

* `Memo.Table.map φ t`: the table with the numbers of `t` under `φ`.

## Main results

* `Memo.Table.get_map`: the image of a table has the images of its numbers.
* `Memo.Table.map_sumOver`, `Memo.Table.map_rename`, `Memo.Table.map_best`, `Memo.Table.map_op`: the operations on tables commute with the image.
-/

@[expose] public section

namespace Memo.Table

variable {K L : Type*} {size : ℕ → ℕ}

/-- The **image of a table** under a map of numbers. -/
def map (φ : K → L) (t : Table K) : Table L := ⟨t.vars, t.data.map φ⟩

@[simp] theorem vars_map (φ : K → L) (t : Table K) : (t.map φ).vars = t.vars := rfl

theorem getD_map {α β : Type*} (h : α → β) {a₀ : α} {b₀ : β} (h0 : h a₀ = b₀) (a : Array α)
    (k : ℕ) : (a.map h).getD k b₀ = h (a.getD k a₀) := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[k]? <;> simp [h0]

theorem map_ofFn (φ : K → L) (vars : List ℕ) (f : (ℕ → ℕ) → K) :
    (ofFn size vars f).map φ = ofFn size vars fun σ ↦ φ (f σ) := by
  simp [map, ofFn]

theorem map_const (φ : K → L) (k : K) : (const k).map φ = const (φ k) := by
  simp [map, const]

section Zero

variable [Zero K] [Zero L] {φ : K → L} (h0 : φ 0 = 0)
include h0

/-- The image of a table has, at every assignment, the image of the number of the table. -/
theorem get_map (t : Table K) (σ : ℕ → ℕ) : (t.map φ).get size σ = φ (t.get size σ) :=
  getD_map φ h0 _ _

theorem map_rename (links : List (ℕ × ℕ)) (t : Table K) :
    (t.map φ).rename size links = (t.rename size links).map φ := by
  unfold Table.rename
  simp only [vars_map]
  by_cases h : (t.vars.all fun i ↦ (links.lookup i).getD i == i) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, map_ofFn, get_map h0]

theorem map_op {k : ℕ} {f : (Fin k → K) → K} {f' : (Fin k → L) → L}
    (hf : ∀ x, f' (fun i ↦ φ (x i)) = φ (f x)) (ts : Fin k → Table K) :
    op size f' (fun i ↦ (ts i).map φ) = (op size f ts).map φ := by
  simp only [Table.op, map_ofFn, vars_map, get_map h0, hf]

end Zero

section Add

variable [AddMonoid K] [AddMonoid L] {φ : K → L} (h0 : φ 0 = 0)
  (hadd : ∀ a b, φ (a + b) = φ a + φ b)
include h0 hadd

omit h0 in
theorem map_foldl_add (g : ℕ → K) (l : List ℕ) (a : K) :
    φ (l.foldl (fun total j ↦ total + g j) a) = l.foldl (fun total j ↦ total + φ (g j)) (φ a) := by
  induction l generalizing a with
  | nil => rfl
  | cons j l ih => rw [List.foldl_cons, List.foldl_cons, ih, hadd]

theorem map_sumOut (i : ℕ) (t : Table K) : (t.map φ).sumOut size i = (t.sumOut size i).map φ := by
  unfold Table.sumOut
  simp only [vars_map]
  by_cases hi : i ∈ t.vars
  · simp only [hi, ↓reduceIte, map_ofFn, get_map h0]
    congr 1
    funext σ
    rw [map_foldl_add hadd, h0]
  · simp only [hi, ↓reduceIte, map, Array.map_map, Table.mk.injEq, true_and]
    congr 1
    funext x
    simp only [Function.comp]
    rw [map_foldl_add hadd (fun _ ↦ x), h0]

theorem map_sumOver (I : List ℕ) (t : Table K) :
    (t.map φ).sumOver size I = (t.sumOver size I).map φ := by
  induction I generalizing t with
  | nil => rfl
  | cons i I ih =>
    show ((t.map φ).sumOut size i).sumOver size I = ((t.sumOut size i).sumOver size I).map φ
    rw [map_sumOut h0 hadd, ih]

end Add

theorem map_best [Semifield K] [Semifield L] [LinearOrder K] [LinearOrder L] (φ : K →+* L)
    (hφ : StrictMono φ) (i : ℕ) (t : Table K) :
    (t.map φ).best size i = (t.best size i).map φ := by
  simp only [Table.best, map_ofFn, vars_map, get_map (map_zero φ), hφ.le_iff_le]
  congr 1
  funext σ
  split_ifs <;> simp

end Memo.Table
