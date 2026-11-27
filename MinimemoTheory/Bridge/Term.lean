/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Term
public import MinimemoTheory.Interp
public import MinimemoTheory.Bridge.Table
public import MinimemoTheory.Belief.Basic

/-!
# Terms as operations on beliefs

This file proves that the terms that the statements of memo are written with act on beliefs as
those statements do.

A table with a set of uncertain choices is a belief, `Memo.Table.toBelief`. The table of the term
of a choice is the belief after the choice, and likewise for an observation, an event and a
forgetting; the table of the term of an expectation is the expectation in the belief. These hold
when the interpretation gives the product and the quotient their meaning, `Memo.Interp.Arith`.

## Main definitions

* `Memo.Table.toBelief size u t`: the belief with uncertain choices `u` and the factor of `t`.

## Main results

* `Memo.Term.toFactor_lit`, `Memo.Term.toFactor_val`, `Memo.Term.toFactor_op`,
  `Memo.Term.toFactor_ref`, `Memo.Term.toFactor_sum`: the factor of the table of a term.
* `Memo.Term.toBelief_chooses`, `Memo.Term.toBelief_choosesMany`, `Memo.Term.toBelief_observes`,
  `Memo.Term.toBelief_weighs`, `Memo.Term.toBelief_forgets`: the tables of the statements.
* `Memo.Term.toFactor_expect`: the table of an expectation is the expectation in the belief.
-/

@[expose] public section

universe u

namespace Memo

variable {D : Type u} {F : ℕ → Type u} {K : Type u} [Semifield K] [LinearOrder K]
  {J : Interp D F K} {size : ℕ → ℕ}

/-- The **belief of a table** with the uncertain choices `u`. -/
abbrev Table.toBelief (size : ℕ → ℕ) (u : Finset ℕ) (t : Table K) :
    Belief (fun i ↦ Fin (size i)) K :=
  ⟨u, Table.toFactor size t⟩

namespace Term

variable {W : Array (Table K)}

/-- The table of a literal has its number at every assignment. -/
theorem toFactor_lit (q : ℚ) (σ : ∀ i, Fin (size i)) :
    Table.toFactor size ((Term.lit q : Term D F).eval J size W) σ = J.lit q := by
  simp [Term.eval, Table.toFactor, Table.get, Table.const, Table.index]

/-- The table of the value of a choice has, at an assignment, the value at the position of the
choice. -/
theorem toFactor_val (i : ℕ) (d : D) (σ : ∀ i, Fin (size i)) :
    Table.toFactor size ((Term.val i d : Term D F).eval J size W) σ = (J.dom d).val (σ i) := by
  rw [Term.eval]
  exact Table.get_ofFn _ _ (fun x _ ↦ (σ x).isLt) fun σ₁ σ₂ h ↦ by rw [h i (by simp)]

/-- The table of a reference is the table that it names. -/
theorem toFactor_ref (w : ℕ) :
    Table.toFactor size ((Term.ref w : Term D F).eval J size W) =
      Table.toFactor size (W.getD w (.const 1)) := rfl

/-- A term read through no links has the table of the term. -/
theorem eval_rename_nil (t : Term D F) : (Term.rename [] t).eval J size W = t.eval J size W := by
  rw [Term.eval, List.filter_nil, Table.rename_nil]

/-- The table of an operator applied to terms has, at an assignment, the value of the operator at
the numbers of their tables. -/
theorem toFactor_op {k : ℕ} (o : Prim k ⊕ F k) (ts : Fin k → Term D F) (σ : ∀ i, Fin (size i)) :
    Table.toFactor size ((Term.op o ts).eval J size W) σ =
      J.op o fun i ↦ Table.toFactor size ((ts i).eval J size W) σ := by
  rw [Term.eval]
  simp only [Table.toFactor]
  rw [Table.get_op _ _ fun i ↦ (σ i).isLt]
  simp

/-- The factor of a sum over distinct choices is the sum of the factor over those choices. -/
theorem toFactor_sum (I : List ℕ) (hI : I.Nodup) (t : Term D F) :
    Table.toFactor size ((Term.sum I t).eval J size W) =
      (Table.toFactor size (t.eval J size W)).sumOver I.toFinset := by
  rw [Term.eval, Table.toFactor_sumOver I hI]

variable (hJ : J.Arith)
include hJ

theorem toFactor_mul (a b : Term D F) :
    Table.toFactor size ((Term.mul a b).eval J size W) =
      Table.toFactor size (a.eval J size W) * Table.toFactor size (b.eval J size W) := by
  funext σ
  rw [Term.mul, Term.app, toFactor_op, hJ.mul]
  rfl

theorem toFactor_div (a b : Term D F) :
    Table.toFactor size ((Term.div a b).eval J size W) =
      Table.toFactor size (a.eval J size W) / Table.toFactor size (b.eval J size W) := by
  funext σ
  rw [Term.div, Term.app, toFactor_op, hJ.div]
  rfl

variable (w : ℕ) (u : Finset ℕ)

/-- The table of a choice of several values is the belief after they are chosen together. -/
theorem toBelief_choosesMany (I : List ℕ) (hI : I.Nodup) (t : Term D F) :
    Table.toBelief size (u ∪ I.toFinset) ((Term.chooses w I t).eval J size W) =
      (Table.toBelief size u (W.getD w (.const 1))).choosesMany I.toFinset
        (Table.toFactor size (t.eval J size W)) := by
  simp only [Table.toBelief, Belief.choosesMany, Term.chooses]
  rw [toFactor_mul hJ, toFactor_div hJ, toFactor_sum I hI, toFactor_ref]

/-- The table of a choice is the belief after the choice. -/
theorem toBelief_chooses (i : ℕ) (t : Term D F) :
    Table.toBelief size (u ∪ {i}) ((Term.chooses w [i] t).eval J size W) =
      (Table.toBelief size u (W.getD w (.const 1))).chooses i
        (Table.toFactor size (t.eval J size W)) := by
  simpa [Belief.chooses_eq_choosesMany] using
    toBelief_choosesMany hJ w u [i] (List.nodup_singleton i) t

/-- The table of an observation is the belief after the observation, if the term sums over the
choices that remain uncertain. -/
theorem toBelief_observes (i : ℕ) (I : List ℕ) (hI : I.Nodup) (hu : I.toFinset = u.erase i) :
    Table.toBelief size (u.erase i) ((Term.observes w I : Term D F).eval J size W) =
      (Table.toBelief size u (W.getD w (.const 1))).observes i := by
  simp only [Table.toBelief, Belief.observes, Term.observes]
  rw [toFactor_div hJ, toFactor_sum I hI, toFactor_ref, hu]

/-- The table of an event is the belief with its factor multiplied by the weight. -/
theorem toBelief_weighs (t : Term D F) :
    Table.toBelief size u ((Term.weighs w t).eval J size W) =
      (Table.toBelief size u (W.getD w (.const 1))).weighs
        (Table.toFactor size (t.eval J size W)) := by
  simp only [Table.toBelief, Belief.weighs, Term.weighs]
  rw [toFactor_mul hJ, toFactor_ref]

omit hJ in
/-- The table of a forgetting is the belief after the choices are forgotten. -/
theorem toBelief_forgets (I : List ℕ) (hI : I.Nodup) :
    Table.toBelief size (u \ I.toFinset) ((Term.forgets w I : Term D F).eval J size W) =
      (Table.toBelief size u (W.getD w (.const 1))).forgets I.toFinset := by
  simp only [Table.toBelief, Belief.forgets, Term.forgets]
  rw [toFactor_sum I hI, toFactor_ref]

/-- The table of an expectation is the expectation of the factor of its term in the belief that
it names, with the choices that it sums over as the uncertain ones. -/
theorem toFactor_expect (I : List ℕ) (hI : I.Nodup) (t : Term D F) :
    Table.toFactor size ((Term.expect w I t).eval J size W) =
      (Table.toBelief size I.toFinset (W.getD w (.const 1))).expect
        (Table.toFactor size (t.eval J size W)) := by
  simp only [Belief.expect, Term.expect]
  rw [toFactor_sum I hI, toFactor_mul hJ, toFactor_ref]

end Term

end Memo
