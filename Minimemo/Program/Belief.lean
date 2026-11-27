/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program.Sized

/-!
# Steps as operations on beliefs

This file proves that the steps of a program act on beliefs as the statements of memo do.

A table with a set of uncertain choices is a belief, `Memo.Table.toBelief`. The table that a step
adds is the belief after the statement of that step: after a choice, an observation, an event, or
a forgetting. The table of an expectation term is the expectation in the belief that it names.
The tables so far are assumed sized, as the tables of a program are.

## Main definitions

* `Memo.Table.toBelief size u t`: the belief with uncertain choices `u` and the factor of `t`.

## Main results

* `Memo.Step.toBelief_chooses`, `Memo.Step.toBelief_choosesMany`: the table of a `chooses` step.
* `Memo.Step.toBelief_observes`: the table of an `observes` step.
* `Memo.Step.toBelief_weighs`, `Memo.Step.toBelief_forgets`: the tables of the other steps.
* `Memo.Term.toFactor_expect`: the table of an expectation term is the expectation in the belief.
-/

@[expose] public section

universe u

namespace Memo

variable {K : Type u} [Semifield K] [LinearOrder K] {size : ℕ → ℕ}

/-- The **belief of a table** with the uncertain choices `u`. -/
abbrev Table.toBelief (size : ℕ → ℕ) (u : Finset ℕ) (t : Table K) :
    Belief (fun i ↦ Fin (size i)) K :=
  ⟨u, Table.toFactor size t⟩

variable {W : Array (Table K)} (hW : ∀ x ∈ W, x.Sized size) (w : ℕ) (u : Finset ℕ)
include hW

namespace Step

/-- The table of a `chooses` step of several choices is the belief after they are made
together. -/
theorem toBelief_choosesMany (I : List ℕ) (hI : I.Nodup) (t : Term K) :
    Table.toBelief size (u ∪ I.toFinset) ((Step.chooses w I t).table size W) =
      (Table.toBelief size u (W.getD w (.const 1))).choosesMany I.toFinset
        (Table.toFactor size (t.eval size W)) := by
  have hw := sized_getD hW w
  have ht := Term.sized_eval t W hW
  simp only [Table.toBelief, Belief.choosesMany, Step.table]
  rw [Table.toFactor_mul hw (ht.div (ht.sumOver _)), Table.toFactor_div ht (ht.sumOver _),
    withSizes, Table.toFactor_sumOver I hI ht]

/-- The table of a `chooses` step of one choice is the belief after the choice. -/
theorem toBelief_chooses (i : ℕ) (t : Term K) :
    Table.toBelief size (u ∪ {i}) ((Step.chooses w [i] t).table size W) =
      (Table.toBelief size u (W.getD w (.const 1))).chooses i
        (Table.toFactor size (t.eval size W)) := by
  simpa [Belief.chooses_eq_choosesMany] using
    toBelief_choosesMany hW w u [i] (List.nodup_singleton i) t

/-- The table of an `observes` step is the belief after the observation, if the step sums over the
choices that remain uncertain. -/
theorem toBelief_observes (i : ℕ) (I : List ℕ) (hI : I.Nodup) (hu : I.toFinset = u.erase i) :
    Table.toBelief size (u.erase i) ((Step.observes w I).table size W) =
      (Table.toBelief size u (W.getD w (.const 1))).observes i := by
  have hw := sized_getD hW w
  simp only [Table.toBelief, Belief.observes, Step.table]
  rw [Table.toFactor_div hw (hw.sumOver _), withSizes, Table.toFactor_sumOver I hI hw, hu]

/-- The table of a `weighs` step is the belief with its factor multiplied by the weight. -/
theorem toBelief_weighs (t : Term K) :
    Table.toBelief size u ((Step.weighs w t).table size W) =
      (Table.toBelief size u (W.getD w (.const 1))).weighs
        (Table.toFactor size (t.eval size W)) := by
  simp only [Table.toBelief, Belief.weighs, Step.table]
  rw [Table.toFactor_mul (sized_getD hW w) (Term.sized_eval t W hW)]

/-- The table of a `forgets` step is the belief after the choices are forgotten. -/
theorem toBelief_forgets (I : List ℕ) (hI : I.Nodup) :
    Table.toBelief size (u \ I.toFinset) ((Step.forgets w I).table size W) =
      (Table.toBelief size u (W.getD w (.const 1))).forgets I.toFinset := by
  simp only [Table.toBelief, Belief.forgets, Step.table]
  rw [withSizes, Table.toFactor_sumOver I hI (sized_getD hW w)]

end Step

/-- The table of an expectation term is the expectation of the factor of its term in the belief of
the table that it names, with the choices that it sums over as the uncertain ones. -/
theorem Term.toFactor_expect (I : List ℕ) (hI : I.Nodup) (t : Term K) :
    Table.toFactor size ((Term.expect w I t).eval size W) =
      (Table.toBelief size I.toFinset (W.getD w (.const 1))).expect
        (Table.toFactor size (t.eval size W)) := by
  have hw := sized_getD hW w
  have ht := Term.sized_eval t W hW
  simp only [Term.eval, Belief.expect]
  rw [withSizes, Table.toFactor_sumOver I hI (ht.mul hw), Table.toFactor_mul ht hw]

end Memo
