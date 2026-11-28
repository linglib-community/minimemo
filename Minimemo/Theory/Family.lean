/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Family

/-!
# The array of a member that refers to one other

A member of a family whose model has one reference has the array of its model, read over the
array of the member that the reference names, one depth below.

## Main results

* `Memo.Family.lookup_fill`: the arrays found for a member include its own.
* `Memo.Family.entries_of_refs_eq_singleton`: the array of a member with one reference.
-/

@[expose] public section

universe u v

namespace Memo

variable {A N D R : Type u} {F : ℕ → Type u} {P : Type v} {K : Type u} [Zero K] [BEq K] [One K]
  [Add K] [LE K] [DecidableLE K] [DecidableEq A] [DecidableEq N] [DecidableEq D] [BEq P]
  [LawfulBEq P] (fam : Family A N D F P R)
  (of : (D → Domain K) → ({k : ℕ} → Refs R F k → (Fin k → K) → K) → Interp D (Refs R F) K)
  (dom : D → Domain K) (fn : {k : ℕ} → F k → (Fin k → K) → K)

/-- The arrays found for a member, starting from none, include its own. -/
theorem Family.lookup_fill (n : ℕ) (p : P) :
    (fam.fill of dom fn (n + 1) p []).lookup p = some (fam.entries of dom fn n p) := by
  rw [Family.fill]
  simp only [List.lookup_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    List.lookup_cons_self]
  rfl

/-- The array of a member with one reference is the array of its model over the array of the
member that the reference names, one depth below. -/
theorem Family.entries_of_refs_eq_singleton {p : P} {r : R} (h : (fam.model p).refs = [r])
    (n : ℕ) :
    ∃ below : P → List K, below (fam.target p r) = fam.entries of dom fn n (fam.target p r) ∧
      fam.entries of dom fn (n + 1) p =
        (Model.entries (of dom (fam.call dom fn below p)) (fam.model p)).getD [] := by
  refine ⟨fun q ↦ ((fam.fill of dom fn (n + 1) (fam.target p r) []).lookup q).getD [], ?_, ?_⟩
  · simp only [fam.lookup_fill of dom fn n, Option.getD_some]
  · rw [Family.entries, Family.interp, h]
    rfl

end Memo
