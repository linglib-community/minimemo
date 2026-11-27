/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program
public import Minimemo.Table.Factor

/-!
# Steps as operations on beliefs

This file proves that the steps of a program act on beliefs as the statements of memo do.

A sized table with a set of uncertain choices is a belief, `Memo.Table.toBelief`. The table that a
`chooses` step adds is the belief after that choice, and the table that an `observes` step adds is
the belief after that observation.

## Main definitions

* `Memo.Table.toBelief size u t`: the belief with uncertain choices `u` and the factor of `t`.

## Main results

* `Memo.Step.toBelief_chooses`: the table of a `chooses` step of one choice is the belief after
  the choice.
* `Memo.Step.toBelief_observes`: the table of an `observes` step is the belief after the
  observation.
* `Memo.Step.toBelief_choosesMany`, `Memo.Step.toBelief_weighs`, `Memo.Step.toBelief_forgets`:
  the tables of the other steps.
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

namespace Step

variable (W : Array (Table K)) (w : ℕ) (u : Finset ℕ)

/-- The table of a `chooses` step of one choice is the belief after the choice: the belief of the
table before it, with the factor of the weight. -/
theorem toBelief_chooses (i : ℕ) (t : Term K) (hw : (W.getD w (.const 1)).Sized size)
    (ht : (t.eval W).Sized size) :
    Table.toBelief size (u ∪ {i}) ((Step.chooses w [(i, size i)] t).table W) =
      (Table.toBelief size u (W.getD w (.const 1))).chooses i (Table.toFactor size (t.eval W)) := by
  simp only [Table.toBelief, Belief.chooses, Step.table]
  rw [Table.toFactor_mul hw (ht.div (ht.sumOver _)), Table.toFactor_div ht (ht.sumOver _),
    Table.toFactor_sumOver_singleton i ht]

/-- The table of an `observes` step is the belief after the observation, if the step sums over the
choices that remain uncertain. -/
theorem toBelief_observes (i : ℕ) (I : List ℕ) (hI : I.Nodup) (hu : I.toFinset = u.erase i)
    (hw : (W.getD w (.const 1)).Sized size) :
    Table.toBelief size (u.erase i)
        ((Step.observes w (I.map fun i ↦ (i, size i))).table W) =
      (Table.toBelief size u (W.getD w (.const 1))).observes i := by
  simp only [Table.toBelief, Belief.observes, Step.table]
  rw [Table.toFactor_div hw (hw.sumOver _), Table.toFactor_sumOver I hI hw, hu]

/-- The table of a `chooses` step of several choices is the belief after they are made
together. -/
theorem toBelief_choosesMany (I : List ℕ) (hI : I.Nodup) (t : Term K)
    (hw : (W.getD w (.const 1)).Sized size) (ht : (t.eval W).Sized size) :
    Table.toBelief size (u ∪ I.toFinset)
        ((Step.chooses w (I.map fun i ↦ (i, size i)) t).table W) =
      (Table.toBelief size u (W.getD w (.const 1))).choosesMany I.toFinset
        (Table.toFactor size (t.eval W)) := by
  simp only [Table.toBelief, Belief.choosesMany, Step.table]
  rw [Table.toFactor_mul hw (ht.div (ht.sumOver _)), Table.toFactor_div ht (ht.sumOver _),
    Table.toFactor_sumOver I hI ht]

/-- The table of a `weighs` step is the belief with its factor multiplied by the weight. -/
theorem toBelief_weighs (t : Term K) (hw : (W.getD w (.const 1)).Sized size)
    (ht : (t.eval W).Sized size) :
    Table.toBelief size u ((Step.weighs w t).table W) =
      (Table.toBelief size u (W.getD w (.const 1))).weighs (Table.toFactor size (t.eval W)) := by
  simp only [Table.toBelief, Belief.weighs, Step.table]
  rw [Table.toFactor_mul hw ht]

/-- The table of a `forgets` step is the belief after the choices are forgotten. -/
theorem toBelief_forgets (I : List ℕ) (hI : I.Nodup) (hw : (W.getD w (.const 1)).Sized size) :
    Table.toBelief size (u \ I.toFinset)
        ((Step.forgets w (I.map fun i ↦ (i, size i))).table W) =
      (Table.toBelief size u (W.getD w (.const 1))).forgets I.toFinset := by
  simp only [Table.toBelief, Belief.forgets, Step.table]
  rw [Table.toFactor_sumOver I hI hw]

end Step

/-- The table of an expectation term is the expectation of the factor of its term in the belief of
the table that it names, if it sums over the uncertain choices of that belief. -/
theorem Term.toFactor_expect (W : Array (Table K)) (w : ℕ) (I : List ℕ) (hI : I.Nodup)
    (t : Term K) (hw : (W.getD w (.const 1)).Sized size) (ht : (t.eval W).Sized size) :
    Table.toFactor size ((Term.expect w (I.map fun i ↦ (i, size i)) t).eval W) =
      (Table.toBelief size I.toFinset (W.getD w (.const 1))).expect
        (Table.toFactor size (t.eval W)) := by
  simp only [Term.eval, Belief.expect]
  rw [Table.toFactor_sumOver I hI (ht.mul hw), Table.toFactor_mul ht hw]

end Memo
