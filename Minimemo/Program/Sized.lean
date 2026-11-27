/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program.Belief

/-!
# Sized programs

This file gives a check on a program and proves that a program that passes it computes sized
tables only.

Fix a size for every choice. A term is sized if every value of a choice in it has the size of that
choice, and every link in it joins two choices of the same size; a step is sized if its term is,
and the choices that it sums over have their sizes. The check is a computation on the program, so
it can be run on the program of a model.

## Main definitions

* `Memo.Term.sized size t`, `Memo.Step.sized size s`, `Memo.Program.sized size p`: the checks.
* `Memo.Program.sizes p`: the size that the program `p` gives each choice where it first mentions
  it.

## Main results

* `Memo.Term.sized_eval`, `Memo.Step.sized_table`: a sized term or step has a sized table, when
  the tables so far are sized.
* `Memo.Program.sized_tables`: every table that a sized program computes is sized.
-/

@[expose] public section

universe u

namespace Memo

variable {K : Type u} {size : ℕ → ℕ}

/-- The choices of a list have their sizes. -/
def sizedVars (size : ℕ → ℕ) (over : List (ℕ × ℕ)) : Bool := over.all fun v ↦ v.2 == size v.1

mutual

/-- A term is **sized** if every value of a choice in it has the size of that choice, and every
link in it joins two choices of the same size. -/
def Term.sized (size : ℕ → ℕ) : Term K → Bool
  | .lit _ => true
  | .op _ ts => (List.finRange _).all fun i ↦ (ts i).sized size
  | .val i n _ => n == size i
  | .expect _ over t => sizedVars size over && t.sized size
  | .rename links t => (links.all fun l ↦ size l.1 == size l.2) && t.sized size
  | .best i n t => n == size i && t.sized size
  | .after s t => s.sized size && t.sized size

/-- A step is **sized** if its term is, and the choices that it sums over have their sizes. -/
def Step.sized (size : ℕ → ℕ) : Step K → Bool
  | .chooses _ over t => sizedVars size over && t.sized size
  | .weighs _ t => t.sized size
  | .observes _ over => sizedVars size over
  | .forgets _ over => sizedVars size over

end

mutual

/-- The choices that a term mentions, each with the size that it is given there. -/
def Term.mentions : Term K → List (ℕ × ℕ)
  | .lit _ => []
  | .op _ ts => (List.finRange _).flatMap fun i ↦ (ts i).mentions
  | .val i n _ => [(i, n)]
  | .expect _ over t => over ++ t.mentions
  | .rename _ t => t.mentions
  | .best i n t => (i, n) :: t.mentions
  | .after s t => s.mentions ++ t.mentions

/-- The choices that a step mentions, each with the size that it is given there. -/
def Step.mentions : Step K → List (ℕ × ℕ)
  | .chooses _ over t => over ++ t.mentions
  | .weighs _ t => t.mentions
  | .observes _ over => over
  | .forgets _ over => over

end

/-- The size of each choice of a program: the size that its first mention gives it, and the size
of the axis for a choice that is an axis. -/
def Program.sizes (p : Program K) (i : ℕ) : ℕ :=
  ((p.axes ++ p.steps.flatMap Step.mentions ++ p.ret.mentions).lookup i).getD 0

/-- A program is **sized** if its steps and its term are. -/
def Program.sized (size : ℕ → ℕ) (p : Program K) : Bool :=
  (p.steps.all fun s ↦ s.sized size) && p.ret.sized size

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

theorem sizedVars_iff {over : List (ℕ × ℕ)} :
    sizedVars size over = true ↔ ∀ v ∈ over, v.2 = size v.1 := by
  simp [sizedVars]

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

/-- A sized term has a sized table, when the tables so far are sized. -/
theorem Term.sized_eval : ∀ (t : Term K) (W : Array (Table K)), (∀ x ∈ W, x.Sized size) →
    t.sized size = true → (t.eval W).Sized size
  | .lit r, _, _, _ => Table.sized_const r
  | .op f ts, W, hW, h => by
    rw [Term.eval]
    refine Table.Sized.op f fun i ↦ ?_
    have hi : (ts i).sized size = true := by
      simp only [Term.sized, List.all_eq_true] at h
      exact h i (List.mem_finRange i)
    have := Term.sized_eval (ts i) W hW hi
    simpa using this
  | .val i n v, _, _, h => by
    rw [Term.eval]
    intro w hw
    simp only [Term.sized, beq_iff_eq] at h
    simp only [Table.ofFn, List.mem_singleton] at hw
    subst hw
    exact h
  | .expect w over t, W, hW, h => by
    simp only [Term.sized, Bool.and_eq_true] at h
    rw [Term.eval]
    exact ((Term.sized_eval t W hW h.2).mul (sized_getD hW w)).sumOver over
  | .rename links t, W, hW, h => by
    simp only [Term.sized, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    rw [Term.eval]
    exact (Term.sized_eval t W hW h.2).rename h.1
  | .best i n t, W, hW, h => by
    simp only [Term.sized, Bool.and_eq_true] at h
    rw [Term.eval]
    exact (Term.sized_eval t W hW h.2).best i n
  | .after s t, W, hW, h => by
    simp only [Term.sized, Bool.and_eq_true] at h
    rw [Term.eval]
    exact Term.sized_eval t _ (sized_push hW (Step.sized_table s W hW h.1)) h.2

/-- A sized step adds a sized table, when the tables so far are sized. -/
theorem Step.sized_table : ∀ (s : Step K) (W : Array (Table K)), (∀ x ∈ W, x.Sized size) →
    s.sized size = true → (s.table W).Sized size
  | .chooses w over t, W, hW, h => by
    simp only [Step.sized, Bool.and_eq_true] at h
    have ht := Term.sized_eval t W hW h.2
    rw [Step.table]
    exact (sized_getD hW w).mul (ht.div (ht.sumOver over))
  | .weighs w t, W, hW, h => by
    rw [Step.table]
    exact (sized_getD hW w).mul (Term.sized_eval t W hW (by simpa [Step.sized] using h))
  | .observes w over, W, hW, _ => by
    rw [Step.table]
    exact (sized_getD hW w).div ((sized_getD hW w).sumOver over)
  | .forgets w over, W, hW, _ => by
    rw [Step.table]
    exact (sized_getD hW w).sumOver over

end

/-- The tables after sized steps are sized. -/
theorem sized_foldl_run (steps : List (Step K)) (hs : ∀ s ∈ steps, s.sized size = true) :
    ∀ x ∈ steps.foldl Step.run #[.const 1], x.Sized size := by
  have key : ∀ (steps : List (Step K)) (W : Array (Table K)), (∀ x ∈ W, x.Sized size) →
      (∀ s ∈ steps, s.sized size = true) → ∀ x ∈ steps.foldl Step.run W, x.Sized size := by
    intro steps
    induction steps with
    | nil => exact fun W hW _ ↦ hW
    | cons s steps ih =>
      intro W hW hs
      exact ih _ (sized_push hW (Step.sized_table s W hW (hs s List.mem_cons_self)))
        fun s' hs' ↦ hs s' (List.mem_cons_of_mem _ hs')
  exact key steps _ (fun x hx ↦ by
    obtain rfl : x = .const 1 := by simpa using hx
    exact Table.sized_const 1) hs

/-- After sized steps, a sized `chooses` step of one choice adds the belief after the choice. -/
theorem Step.toBelief_chooses_of_sized (pre : List (Step K))
    (hpre : ∀ s ∈ pre, s.sized size = true) (w i : ℕ) (t : Term K) (ht : t.sized size = true)
    (u : Finset ℕ) :
    Table.toBelief size (u ∪ {i})
        ((Step.chooses w [(i, size i)] t).table (pre.foldl Step.run #[.const 1])) =
      (Table.toBelief size u ((pre.foldl Step.run #[.const 1]).getD w (.const 1))).chooses i
        (Table.toFactor size (t.eval (pre.foldl Step.run #[.const 1]))) :=
  Step.toBelief_chooses _ w u i t (sized_getD (sized_foldl_run pre hpre) w)
    (Term.sized_eval t _ (sized_foldl_run pre hpre) ht)

/-- After sized steps, an `observes` step adds the belief after the observation, if it sums over
the choices that remain uncertain. -/
theorem Step.toBelief_observes_of_sized (pre : List (Step K))
    (hpre : ∀ s ∈ pre, s.sized size = true) (w i : ℕ) (I : List ℕ) (hI : I.Nodup)
    (u : Finset ℕ) (hu : I.toFinset = u.erase i) :
    Table.toBelief size (u.erase i)
        ((Step.observes w (I.map fun i ↦ (i, size i))).table (pre.foldl Step.run #[.const 1])) =
      (Table.toBelief size u ((pre.foldl Step.run #[.const 1]).getD w (.const 1))).observes i :=
  Step.toBelief_observes _ w u i I hI hu (sized_getD (sized_foldl_run pre hpre) w)

/-- Every table that a sized program computes is sized. -/
theorem Program.sized_tables {p : Program K} (h : p.sized size = true) :
    ∀ x ∈ p.steps.foldl Step.run #[.const 1], x.Sized size := by
  simp only [Program.sized, Bool.and_eq_true, List.all_eq_true] at h
  exact sized_foldl_run p.steps h.1

/-- The table that a sized program returns is sized. -/
theorem Program.sized_table {p : Program K} (h : p.sized size = true) : p.table.Sized size := by
  have h' := h
  simp only [Program.sized, Bool.and_eq_true] at h'
  exact Term.sized_eval _ _ (Program.sized_tables h) h'.2

end Memo
