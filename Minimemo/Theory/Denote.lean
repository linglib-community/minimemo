/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Theory.Bridge.Table
public import Minimemo.Theory.Transfer

/-!
# The meaning of a term

This file gives a term its meaning as a number that depends on the assignment, and proves that
the stored table of the term has that number.

The meaning is defined on the term alone: a sum is a sum over positions, a reference is a function
given for an earlier table, and nothing is stored. So the meaning of a given term can be unfolded
to an expression in the numbers of the model, where a stored table cannot.

## Main definitions

* `Memo.sumList size over f`: the sum of `f` over the positions of the choices in `over`.
* `Memo.Term.denote I size Φ t`: the meaning of the term `t`, when `Φ` gives the meanings of the
  tables so far.

## Main results

* `Memo.Term.get_eval`: the table of a term has, at every assignment in range, the meaning of the
  term.
-/

@[expose] public section

universe u

namespace Memo

variable {D : Type u} {F : ℕ → Type u} {K : Type u} (I : Interp D F K) (size : ℕ → ℕ)

/-- The sum of a number that depends on the assignment, over the positions of the choices in a
list. -/
def sumList [AddCommMonoid K] : List ℕ → ((ℕ → ℕ) → K) → (ℕ → ℕ) → K
  | [], f => f
  | i :: is, f => sumList is fun σ ↦ ∑ j ∈ Finset.range (size i), f (Function.update σ i j)

variable [Semifield K] [LinearOrder K]

/-- The **meaning of a term**: a number that depends on the assignment, when `Φ` gives the meanings
of the tables so far. -/
def Term.denote (Φ : List ((ℕ → ℕ) → K)) : Term D F → (ℕ → ℕ) → K
  | .lit q => fun _ ↦ I.lit q
  | .op o ts => fun σ ↦ I.op o fun i ↦ (ts i).denote Φ σ
  | .val i d => fun σ ↦ (I.dom d).val (σ i)
  | .ref w => Φ.getD w fun _ ↦ 1
  | .sum over t => sumList size over (t.denote Φ)
  | .rename links t => fun σ ↦
    t.denote Φ fun i ↦ σ (((links.filter fun l ↦ size l.1 == size l.2).lookup i).getD i)
  | .best i t => fun σ ↦
    if (List.range (size i)).all fun j ↦ t.denote Φ (Function.update σ i j) ≤ t.denote Φ σ
    then 1 else 0
  | .letE t₁ t₂ => t₂.denote (Φ ++ [t₁.denote Φ])

variable {I size}

/-- An assignment is in range if it gives every choice a position below its size. -/
def InRange (size : ℕ → ℕ) (σ : ℕ → ℕ) : Prop := ∀ i, σ i < size i

theorem InRange.update {σ : ℕ → ℕ} (h : InRange size σ) {i j : ℕ} (hj : j < size i) :
    InRange size (Function.update σ i j) := fun k ↦ by
  by_cases hk : k = i
  · subst hk
    simpa using hj
  · simpa [Function.update, hk] using h k

theorem size_lookup_filter (links : List (ℕ × ℕ)) (i : ℕ) :
    size (((links.filter fun l ↦ size l.1 == size l.2).lookup i).getD i) = size i := by
  induction links with
  | nil => rfl
  | cons l links ih =>
    by_cases hl : size l.1 = size l.2
    · rw [List.filter_cons_of_pos (by simpa using hl), List.lookup_cons]
      by_cases hi : i = l.1
      · subst hi
        simp [hl]
      · have hb : (i == l.1) = false := beq_false_of_ne hi
        simp only [hb]
        exact ih
    · rw [List.filter_cons_of_neg (by simpa using hl)]
      exact ih

omit [LinearOrder K] in
theorem sumList_congr {f g : (ℕ → ℕ) → K} (over : List ℕ)
    (h : ∀ σ, InRange size σ → f σ = g σ) :
    ∀ σ, InRange size σ → sumList size over f σ = sumList size over g σ := by
  induction over generalizing f g with
  | nil => exact h
  | cons i is ih =>
    exact ih fun σ hσ ↦ Finset.sum_congr rfl fun j hj ↦
      h _ (hσ.update (Finset.mem_range.1 hj))

omit [LinearOrder K] in
/-- The sum of a table over a list of variables has, at an assignment in range, the sum of its
numbers over their positions. -/
theorem Table.get_sumOver (over : List ℕ) (t : Table K) :
    ∀ σ, InRange size σ → (t.sumOver size over).get size σ =
      sumList size over (t.get size) σ := by
  induction over generalizing t with
  | nil => exact fun _ _ ↦ rfl
  | cons i is ih =>
    intro σ hσ
    show ((t.sumOut size i).sumOver size is).get size σ = _
    rw [ih _ σ hσ]
    exact sumList_congr is (fun σ hσ ↦ Table.get_sumOut i t hσ) σ hσ

/-- The table of the places where `t` is greatest along a variable has the number one where it
is, at an assignment in range. -/
theorem Table.get_best (i : ℕ) (t : Table K) {σ : ℕ → ℕ} (hσ : InRange size σ) :
    (t.best size i).get size σ =
      if (List.range (size i)).all fun j ↦
        t.get size (Function.update σ i j) ≤ t.get size σ then 1 else 0 := by
  refine Table.get_ofFn _ _ (fun i _ ↦ hσ i) fun σ₁ σ₂ h ↦ ?_
  have hget : t.get size σ₁ = t.get size σ₂ := t.get_congr h
  have hupd (j : ℕ) : t.get size (Function.update σ₁ i j) = t.get size (Function.update σ₂ i j) :=
    t.get_congr fun v hv ↦ by
      by_cases hvi : v = i
      · simp [hvi]
      · simpa [Function.update, hvi] using h v hv
  simp only [hget, hupd]

/-- The tables so far have the meanings in `Φ`, at every assignment in range. -/
def Env (size : ℕ → ℕ) (W : Array (Table K)) (Φ : List ((ℕ → ℕ) → K)) : Prop :=
  Φ.length = W.size ∧ ∀ k σ, InRange size σ →
    (W.getD k (.const 1)).get size σ = Φ.getD k (fun _ ↦ 1) σ

omit [LinearOrder K] in
theorem Env.push {W : Array (Table K)} {Φ : List ((ℕ → ℕ) → K)} (h : Env size W Φ)
    {T : Table K} {f : (ℕ → ℕ) → K} (hT : ∀ σ, InRange size σ → T.get size σ = f σ) :
    Env size (W.push T) (Φ ++ [f]) := by
  refine ⟨by simp [h.1], fun k σ hσ ↦ ?_⟩
  rcases Nat.lt_trichotomy k W.size with hk | hk | hk
  · have := h.2 k σ hσ
    simpa [Array.getD_eq_getD_getElem?, Array.getElem?_push, hk.ne, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (h.1 ▸ hk), hk] using this
  · subst hk
    have h1 : (W.push T)[W.size]? = some T := by simp
    have h2 : (Φ ++ [f])[W.size]? = some f := by rw [← h.1]; simp
    simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, h1, h2, Option.getD_some]
    exact hT σ hσ
  · have h1 : (W.push T)[k]? = none :=
      Array.getElem?_eq_none (by simp only [Array.size_push]; omega)
    have hlen : (Φ ++ [f]).length ≤ k := by
      have := h.1
      simp only [List.length_append, List.length_singleton]
      omega
    have h2 : (Φ ++ [f])[k]? = none := List.getElem?_eq_none hlen
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, h1, h2, Table.get, Table.const,
      Table.index]

omit [LinearOrder K] in
/-- At the start, the only table is the number one. -/
theorem Env.one : Env size (#[.const 1] : Array (Table K)) [fun _ ↦ 1] := by
  refine ⟨rfl, fun k σ _ ↦ ?_⟩
  match k with
  | 0 => simp [Table.get, Table.const, Table.index]
  | k + 1 => simp [Table.get, Table.const, Table.index]

/-- The table of a term has, at every assignment in range, the meaning of the term. -/
theorem Term.get_eval : ∀ (t : Term D F) (W : Array (Table K)) (Φ : List ((ℕ → ℕ) → K)),
    Env size W Φ → ∀ σ, InRange size σ →
      (t.eval I size W).get size σ = t.denote I size Φ σ
  | .lit q, W, Φ, _, σ, _ => by
    simp [Term.eval, Term.denote, Table.get, Table.const, Table.index]
  | .op o ts, W, Φ, h, σ, hσ => by
    rw [Term.eval_op, Table.get_op _ _ hσ, Term.denote]
    congr 1
    funext i
    exact Term.get_eval (ts i) W Φ h σ hσ
  | .val i d, W, Φ, _, σ, hσ => by
    rw [Term.eval, Term.denote]
    exact Table.get_ofFn _ _ (fun x _ ↦ hσ x) fun σ₁ σ₂ h ↦ by rw [h i (by simp)]
  | .ref w, W, Φ, h, σ, hσ => by
    rw [Term.eval, Term.denote]
    exact h.2 w σ hσ
  | .sum over t, W, Φ, h, σ, hσ => by
    rw [Term.eval, Term.denote, Table.get_sumOver over _ σ hσ]
    exact sumList_congr over (fun σ hσ ↦ Term.get_eval t W Φ h σ hσ) σ hσ
  | .rename links t, W, Φ, h, σ, hσ => by
    rw [Term.eval, Term.denote, Table.get_rename _ _ hσ]
    exact Term.get_eval t W Φ h _ fun i ↦ by
      have := hσ (((links.filter fun l ↦ size l.1 == size l.2).lookup i).getD i)
      rwa [size_lookup_filter (size := size)] at this
  | .best i t, W, Φ, h, σ, hσ => by
    have hall : ∀ j ∈ List.range (size i),
        (t.eval I size W).get size (Function.update σ i j) =
          t.denote I size Φ (Function.update σ i j) :=
      fun j hj ↦ Term.get_eval t W Φ h _ (hσ.update (List.mem_range.1 hj))
    rw [Term.eval, Term.denote, Table.get_best i _ hσ, Term.get_eval t W Φ h σ hσ]
    refine if_congr ?_ rfl rfl
    simp only [List.all_eq_true, decide_eq_true_eq]
    exact forall₂_congr fun j hj ↦ by rw [hall j hj]
  | .letE t₁ t₂, W, Φ, h, σ, hσ => by
    rw [Term.eval, Term.denote]
    exact Term.get_eval t₂ _ _ (h.push fun σ hσ ↦ Term.get_eval t₁ W Φ h σ hσ) σ hσ

end Memo
