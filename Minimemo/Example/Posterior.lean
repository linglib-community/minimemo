/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Compile
public import Minimemo.Program.Measure
public import Minimemo.Example.NaiveListener

/-!
# The belief of a listener is a posterior

This file takes a listener with any utterances, any referents and any speaker, with real numbers,
and proves from the program of the model that the belief of the listener is the posterior of
probability theory.

A listener thinks that a speaker chooses a referent uniformly and then an utterance with weight
`w u r`, and observes the utterance. The program of this model has three steps. After the first
two, the belief of the listener is the joint measure of the referent and the utterance: the
measure of the referent with the kernel of the speaker. After the third it is that joint measure
conditioned on the utterance, as a measure on the referent.

Nothing is evaluated: the domains and the weight are arbitrary, and the results follow from the
theorems about steps.

## Main definitions

* `Memo.Posterior.model dom w`: the model.
* `Memo.Posterior.thinks dom w`, `Memo.Posterior.observes dom w`: the tables after the listener
  thinks about the speaker, and after the listener observes the utterance.

## Main results

* `Memo.Posterior.steps_eq`, `Memo.Posterior.tables_eq`: the steps of the program of the model,
  and its tables.
* `Memo.Posterior.said_apply`: the weight of the utterance in the program is `w`.
* `Memo.Posterior.measure_joint`: after the two choices, the belief of the listener is the joint
  measure of the referent and the utterance.
* `Memo.Posterior.measure_posterior`: after the observation, the belief of the listener is the
  joint measure conditioned on the utterance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Memo.Posterior

open NaiveListener (Agent Name Dom)

noncomputable section

variable (dom : Dom → Domain ℝ≥0) (w : ℝ≥0 → ℝ≥0 → ℝ≥0)

/-- A listener thinks that a speaker chooses a referent uniformly and then an utterance with weight
`w u r`, and observes the utterance:
```
listener: thinks[
  speaker: chooses(r_true in R, wpp=1),
  speaker: chooses(u_said in U, wpp=w(u_said, r_true)) ]
listener: observes [speaker.u_said] is u
```
-/
def model : Model Agent Name Dom ℝ≥0 where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U (.op₂ w (.choice .uSaid) (.choice .rTrue))) ;;
    .observes .listener .speaker .uSaid .self .u
  ret := .lit 0

/-- The sizes of the choices of the model: the axes `0` and `1`, and the referent `2` and the
utterance `3` that the listener thinks the speaker chooses. -/
def size (i : ℕ) : ℕ :=
  ([(dom .U).size, (dom .R).size, (dom .R).size, (dom .U).size] : List ℕ).getD i 0

/-- The steps of the program of the model. -/
def steps : List (Step ℝ≥0) := ((Model.program dom (model w)).map (·.steps)).getD []

/-- The weight of the step `k`, if it is a choice. -/
def weight (k : ℕ) : Term ℝ≥0 :=
  match (steps dom w)[k]? with
  | some (.chooses _ _ t) => t
  | _ => .lit 0

/-- The program has three steps: the speaker's choice of the referent `2`, the speaker's choice of
the utterance `3`, and the listener's observation, which leaves the referent uncertain. -/
theorem steps_eq :
    steps dom w = [.chooses 0 [2] (weight dom w 0), .chooses 1 [3] (weight dom w 1),
      .observes 2 [2]] := rfl

theorem sizes_eq : (Model.program dom (model w)).map (·.sizes) =
    some [(dom .U).size, (dom .R).size, (dom .R).size, (dom .U).size] := rfl

/-- The tables after the listener thinks that the speaker chooses the referent. -/
def prior : Array (Table ℝ≥0) :=
  Step.run (size dom) #[.const 1] (.chooses 0 [2] (weight dom w 0))

/-- The tables after the listener thinks that the speaker chooses the utterance. -/
def thinks : Array (Table ℝ≥0) :=
  Step.run (size dom) (prior dom w) (.chooses 1 [3] (weight dom w 1))

/-- The table after the listener observes the utterance. -/
def observes : Table ℝ≥0 := (Step.observes 2 [2]).table (size dom) (thinks dom w)

/-- The tables of the program are the tables after the listener thinks, with the table after the
listener observes. -/
theorem tables_eq :
    (steps dom w).foldl (Step.run (size dom)) #[.const 1] =
      (thinks dom w).push (observes dom w) := rfl

theorem sized_prior : ∀ x ∈ prior dom w, x.Sized (size dom) :=
  sized_foldl_run [.chooses 0 [2] (weight dom w 0)]

theorem sized_thinks : ∀ x ∈ thinks dom w, x.Sized (size dom) :=
  sized_foldl_run [.chooses 0 [2] (weight dom w 0), .chooses 1 [3] (weight dom w 1)]

/-- The weight of the utterance in the program is `w` at the values of the utterance and of the
referent. -/
theorem said_apply {W : Array (Table ℝ≥0)} (hW : ∀ x ∈ W, x.Sized (size dom))
    (σ : ∀ i, Fin (size dom i)) :
    Table.toFactor (size dom) ((weight dom w 1).eval (size dom) W) σ =
      w ((dom .U).val (σ 3)) ((dom .R).val (σ 2)) := by
  show Table.toFactor (size dom)
    ((Term.rename [] (Term.op (fun v ↦ w (v 0) (v 1)) _)).eval (size dom) W) σ = _
  rw [Term.eval_rename_nil, Term.toFactor_op hW]
  show w (Table.toFactor (size dom) ((Term.val 3 (dom .U).val).eval (size dom) W) σ)
    (Table.toFactor (size dom) ((Term.val 2 (dom .R).val).eval (size dom) W) σ) = _
  rw [Term.toFactor_val, Term.toFactor_val]

/-- The table after the first choice has no variables: the referent is chosen uniformly. -/
theorem vars_prior : ((prior dom w).getD 1 (.const 1)).vars = [] := rfl

/-- After the two choices of the speaker, the belief of the listener is the joint measure of the
referent and the utterance: the measure of the referent with the kernel of the speaker. -/
theorem measure_joint (σ : ∀ i, Fin (size dom i)) :
    (Table.toBelief (size dom) ({2} ∪ {3}) ((thinks dom w).getD 2 (.const 1))).measure σ =
      ((Table.toBelief (size dom) {2} ((prior dom w).getD 1 (.const 1))).measure σ ⊗ₘ
        Kernel.ofFunOfCountable fun τ ↦
          ((Belief.choice 3 (Table.toFactor (size dom)
            ((weight dom w 1).eval (size dom) (prior dom w)))).measure
              (Function.updateFinset σ {2} τ) :
            Measure (∀ j : ({3} : Finset ℕ), Fin (size dom j)))).map
        (Equiv.piFinsetUnion (fun i ↦ Fin (size dom i))
          (Finset.disjoint_singleton_right.2 (by decide : (3 : ℕ) ∉ ({2} : Finset ℕ)))) :=
  Step.measure_chooses (sized_prior dom w) 1 {2} 3 (weight dom w 1) (by decide)
    (by rw [vars_prior]; simp) σ

/-- After the observation, the belief of the listener is the joint measure conditioned on the
utterance, as a measure on the referent. -/
theorem measure_posterior (σ : ∀ i, Fin (size dom i)) :
    (Table.toBelief (size dom) (({2} ∪ {3} : Finset ℕ).erase 3) (observes dom w)).measure σ =
      (((Table.toBelief (size dom) ({2} ∪ {3}) ((thinks dom w).getD 2 (.const 1))).measure σ)[|
          {τ | τ ⟨3, by simp⟩ = σ 3}]).map
        (Finset.restrict₂ (π := fun i ↦ Fin (size dom i))
          (Finset.erase_subset 3 ({2} ∪ {3} : Finset ℕ))) :=
  Step.measure_observes (sized_thinks dom w) 2 ({2} ∪ {3}) 3 [2] (List.nodup_singleton 2)
    (by decide) (by decide) σ

end

end Memo.Posterior
