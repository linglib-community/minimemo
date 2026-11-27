/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program.Basic
public import Minimemo.Table.Factor

/-!
# The tables of a program are sized

This file proves that every table that a program computes has, for each of its variables, the
size that the program gives that choice.

## Main results

* `Memo.Term.sized_eval`, `Memo.Step.sized_table`: the table of a term or a step is sized, when
  the tables so far are.
* `Memo.Program.sized_tables`: every table that a program computes is sized.
-/

@[expose] public section

universe u

namespace Memo

variable {K : Type u} {size : ℕ → ℕ}

namespace Table

theorem size_lookup {links : List (ℕ × ℕ)} (h : ∀ l ∈ links, size l.1 = size l.2) (i : ℕ) :
    size ((links.lookup i).getD i) = size i := by
  induction links with
  | nil => rfl
  | cons l links ih =>
    rw [List.lookup_cons]
    by_cases hi : i = l.1
    · subst hi
      simp [(h l List.mem_cons_self).symm]
    · have hb : (i == l.1) = false := beq_false_of_ne hi
      simp only [hb]
      exact ih fun l' hl' ↦ h l' (List.mem_cons_of_mem _ hl')

theorem Sized.rename [Zero K] {t : Table K} {links : List (ℕ × ℕ)} (ht : t.Sized size)
    (h : ∀ l ∈ links, size l.1 = size l.2) : (t.rename links).Sized size := by
  unfold Table.rename
  dsimp only
  split_ifs
  · exact ht
  · intro v hv
    obtain ⟨v₀, hv₀, rfl⟩ := List.mem_map.1 (mem_distinct hv)
    simp only [size_lookup h, ht v₀ hv₀]

theorem Sized.best [Zero K] [One K] [LinearOrder K] {t : Table K} (i n : ℕ) (ht : t.Sized size) :
    (t.best i n).Sized size := ht

theorem mem_foldl_union {α : Type*} (g : α → List (ℕ × ℕ)) (l : List α) (acc : List (ℕ × ℕ))
    {v : ℕ × ℕ} (hv : v ∈ l.foldl (fun vars i ↦ union vars (g i)) acc) :
    v ∈ acc ∨ ∃ i ∈ l, v ∈ g i := by
  induction l generalizing acc with
  | nil => exact .inl hv
  | cons a l ih =>
    rcases ih _ hv with h | ⟨i, hi, h⟩
    · rcases List.mem_append.1 (mem_distinct h) with h | h
      · exact .inl h
      · exact .inr ⟨a, List.mem_cons_self, h⟩
    · exact .inr ⟨i, List.mem_cons_of_mem _ hi, h⟩

theorem Sized.op [Zero K] {k : ℕ} (f : (Fin k → K) → K) {ts : Fin k → Table K}
    (h : ∀ i, (ts i).Sized size) : (Table.op f ts).Sized size := fun v hv ↦ by
  rcases mem_foldl_union (fun i ↦ (ts i).vars) _ _ hv with h' | ⟨i, _, h'⟩
  · simp at h'
  · exact h i v h'

end Table

theorem sized_getD [One K] {W : Array (Table K)} (hW : ∀ x ∈ W, x.Sized size) (w : ℕ) :
    (W.getD w (.const 1)).Sized size := by
  rw [Array.getD_eq_getD_getElem?]
  cases h : W[w]? with
  | none => exact Table.sized_const 1
  | some x => exact hW x (Array.mem_of_getElem? h)

theorem sized_push {W : Array (Table K)} (hW : ∀ x ∈ W, x.Sized size) {t : Table K}
    (ht : t.Sized size) : ∀ x ∈ W.push t, x.Sized size := fun x hx ↦ by
  rcases Array.mem_push.1 hx with h | rfl
  · exact hW x h
  · exact ht

variable [Semifield K] [LinearOrder K]

mutual

/-- The table of a term is sized, when the tables so far are sized. -/
theorem Term.sized_eval : ∀ (t : Term K) (W : Array (Table K)), (∀ x ∈ W, x.Sized size) →
    (t.eval size W).Sized size
  | .lit r, _, _ => Table.sized_const r
  | .op f ts, W, hW => by
    rw [Term.eval]
    refine Table.Sized.op f fun i ↦ ?_
    simpa using Term.sized_eval (ts i) W hW
  | .val i v, _, _ => by
    rw [Term.eval]
    intro w hw
    obtain rfl : w = (i, size i) := by simpa [Table.ofFn] using hw
    rfl
  | .expect w over t, W, hW => by
    rw [Term.eval]
    exact ((Term.sized_eval t W hW).mul (sized_getD hW w)).sumOver _
  | .rename links t, W, hW => by
    rw [Term.eval]
    exact (Term.sized_eval t W hW).rename fun l hl ↦ by simpa using (List.mem_filter.1 hl).2
  | .best i t, W, hW => by
    rw [Term.eval]
    exact (Term.sized_eval t W hW).best i _
  | .after s t, W, hW => by
    rw [Term.eval]
    exact Term.sized_eval t _ (sized_push hW (Step.sized_table s W hW))

/-- The table that a step adds is sized, when the tables so far are sized. -/
theorem Step.sized_table : ∀ (s : Step K) (W : Array (Table K)), (∀ x ∈ W, x.Sized size) →
    (s.table size W).Sized size
  | .chooses w over t, W, hW => by
    have ht := Term.sized_eval t W hW
    rw [Step.table]
    exact (sized_getD hW w).mul (ht.div (ht.sumOver _))
  | .weighs w t, W, hW => by
    rw [Step.table]
    exact (sized_getD hW w).mul (Term.sized_eval t W hW)
  | .observes w over, W, hW => by
    rw [Step.table]
    exact (sized_getD hW w).div ((sized_getD hW w).sumOver _)
  | .forgets w over, W, hW => by
    rw [Step.table]
    exact (sized_getD hW w).sumOver _

end

/-- The tables after any steps are sized. -/
theorem sized_foldl_run (steps : List (Step K)) :
    ∀ x ∈ steps.foldl (Step.run size) #[.const 1], x.Sized size := by
  have key : ∀ (steps : List (Step K)) (W : Array (Table K)), (∀ x ∈ W, x.Sized size) →
      ∀ x ∈ steps.foldl (Step.run size) W, x.Sized size := by
    intro steps
    induction steps with
    | nil => exact fun W hW ↦ hW
    | cons s steps ih => exact fun W hW ↦ ih _ (sized_push hW (Step.sized_table s W hW))
  exact key steps _ fun x hx ↦ by
    obtain rfl : x = .const 1 := by simpa using hx
    exact Table.sized_const 1

/-- Every table that a program computes is sized. -/
theorem Program.sized_tables (p : Program K) :
    ∀ x ∈ p.steps.foldl (Step.run p.size) #[.const 1], x.Sized p.size :=
  sized_foldl_run p.steps

/-- The table that a program returns is sized. -/
theorem Program.sized_table (p : Program K) : p.table.Sized p.size :=
  Term.sized_eval _ _ p.sized_tables

end Memo
