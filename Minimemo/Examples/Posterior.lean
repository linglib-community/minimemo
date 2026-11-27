/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Model
public import Minimemo.Theory.Bridge.Measure
public import Minimemo.Examples.NaiveListener
public import Mathlib.Basic.Real.Basic

/-!
# The belief of a listener is a posterior

This file takes a listener with any utterances, any referents and any speaker whose weights are
nonnegative, with real numbers, and proves from the program of the model that the belief of the
listener is the posterior of probability theory.

A listener thinks that a speaker chooses a referent uniformly and then an utterance with weight
`w u r`, and observes the utterance. The program of this model adds five tables. After the two
choices, the belief of the listener is the joint measure of the referent and the utterance: the
measure of the referent with the kernel of the speaker. After the observation it is that joint
measure conditioned on the utterance, as a measure on the referent.

Nothing is evaluated: the domains and the weight are arbitrary, and the results follow from the
theorems about terms.

## Main definitions

* `Memo.Posterior.model`: the model.
* `Memo.Posterior.interp dom w`: its interpretation, with any domains and any weight `w`.
* `Memo.Posterior.prior dom w`, `Memo.Posterior.joint dom w`, `Memo.Posterior.posterior dom w`: the
  tables of the listener's belief after each statement.

## Main results

* `Memo.Posterior.steps_eq`: the terms of the tables of the program of the model.
* `Memo.Posterior.said_apply`: the weight of the utterance in the program is `w`.
* `Memo.Posterior.measure_joint`: after the two choices, the belief of the listener is the joint
  measure of the referent and the utterance.
* `Memo.Posterior.measure_posterior`: after the observation, the belief of the listener is the
  joint measure conditioned on the utterance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Memo.Posterior

open NaiveListener (Agent Name Dom)

noncomputable section

variable (dom : Dom → Domain ℝ) (w : ℝ → ℝ → ℝ)

/-- The outside function of the model: the weight of an utterance at a referent. -/
inductive Fn : ℕ → Type
  | w : Fn 2
  deriving DecidableEq

/-- A listener thinks that a speaker chooses a referent uniformly and then an utterance with weight
`w u r`, and observes the utterance:
```
listener: thinks[
  speaker: chooses(r_true in R, wpp=1),
  speaker: chooses(u_said in U, wpp=w(u_said, r_true)) ]
listener: observes [speaker.u_said] is u
```
-/
def model : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U (.call .w ![.choice .uSaid, .choice .rTrue])) ;;
    .observes .listener .speaker .uSaid .self .u
  ret := .lit 0

/-- The meaning of the outside function: the weight `w`. -/
def call : {k : ℕ} → Fn k → (Fin k → ℝ) → ℝ
  | _, .w, v => w (v 0) (v 1)

/-- The interpretation of the model with real numbers: any domains and any weight `w`. -/
def interp : Interp Dom Fn ℝ := .ofField dom (call w)

theorem arith : (interp dom w).Arith := Interp.arith_ofField _ _

/-- The sizes of the choices of the model: the axes `0` and `1`, and the referent `2` and the
utterance `3` that the listener thinks the speaker chooses. Every other number has the size one. -/
def size (i : ℕ) : ℕ :=
  ([(dom .U).size, (dom .R).size, (dom .R).size, (dom .U).size] : List ℕ).getD i 1

/-- The sizes of the model are those of its program. -/
theorem size_eq (p : Program Dom Fn) (hp : Model.program model = .ok p) :
    p.size (interp dom w) = size dom := by
  obtain rfl := Except.ok.inj hp
  funext i
  match i with
  | 0 | 1 | 2 | 3 => rfl
  | i + 4 => rfl

omit w in
/-- There is an assignment of a position to every choice, when the two domains are not empty: the
results about assignments are about something. -/
theorem nonempty_assignment (hU : 0 < (dom .U).size) (hR : 0 < (dom .R).size) :
    Nonempty (∀ i, Fin (size dom i)) :=
  ⟨fun i ↦ ⟨0, by
    match i with
    | 0 | 3 => exact hU
    | 1 | 2 => exact hR
    | i + 4 => exact Nat.one_pos⟩⟩

/-- The terms of the tables of the program of the model. -/
def steps : List (Term Dom Fn) := ((Model.program model).toOption.map (·.steps)).getD []

/-- The weight of the referent in the program: the table `1`. -/
def one : Term Dom Fn := steps[0]?.getD (.lit 0)

/-- The weight of the utterance in the program: the table `3`. -/
def said : Term Dom Fn := steps[2]?.getD (.lit 0)

/-- The program adds five tables: the weight of the referent, the belief after the speaker's
choice of the referent `2`, the weight of the utterance, the belief after the speaker's choice of
the utterance `3`, and the belief after the listener's observation, which leaves the referent
uncertain. -/
theorem steps_eq :
    steps = [one, Term.chooses 0 [2] (.ref 1), said, Term.chooses 2 [3] (.ref 3),
      Term.observes 4 [2]] := rfl

theorem doms_eq : (Model.program model).toOption.map (·.doms) = some [.U, .R, .R, .U] := rfl

/-- The table `1`: the weight of the referent. -/
def weight₁ : Table ℝ := one.eval (interp dom w) (size dom) #[.const 1]

/-- The table `2`: the belief of the listener after the speaker's choice of the referent. -/
def prior : Table ℝ :=
  (Term.chooses 0 [2] (.ref 1) : Term Dom Fn).eval (interp dom w) (size dom)
    #[.const 1, weight₁ dom w]

/-- The table `3`: the weight of the utterance. -/
def weight₂ : Table ℝ :=
  said.eval (interp dom w) (size dom) #[.const 1, weight₁ dom w, prior dom w]

/-- The tables `0` to `3`, from which the joint belief is computed. -/
def tables₃ : Array (Table ℝ) := #[.const 1, weight₁ dom w, prior dom w, weight₂ dom w]

/-- The table `4`: the belief of the listener after the speaker's choice of the utterance. -/
def joint : Table ℝ :=
  (Term.chooses 2 [3] (.ref 3) : Term Dom Fn).eval (interp dom w) (size dom) (tables₃ dom w)

/-- The tables `0` to `4`, from which the posterior is computed. -/
def tables₄ : Array (Table ℝ) := (tables₃ dom w).push (joint dom w)

/-- The table `5`: the belief of the listener after it observes the utterance. -/
def posterior : Table ℝ :=
  (Term.observes 4 [2] : Term Dom Fn).eval (interp dom w) (size dom) (tables₄ dom w)

/-- The weight of the referent in the program is one. -/
theorem one_apply (W : Array (Table ℝ)) (σ : ∀ i, Fin (size dom i)) :
    Table.toFactor (size dom) (one.eval (interp dom w) (size dom) W) σ = 1 := by
  show Table.toFactor (size dom)
    ((Term.rename [] (Term.lit 1)).eval (interp dom w) (size dom) W) σ = _
  rw [Term.eval_rename_nil, Term.toFactor_lit]
  exact Rat.cast_one

/-- The weight of the utterance in the program is `w` at the values of the utterance and of the
referent. -/
theorem said_apply (W : Array (Table ℝ)) (σ : ∀ i, Fin (size dom i)) :
    Table.toFactor (size dom) (said.eval (interp dom w) (size dom) W) σ =
      w ((dom .U).val (σ 3)) ((dom .R).val (σ 2)) := by
  show Table.toFactor (size dom)
    ((Term.rename [] (Term.op (.inr Fn.w) _)).eval (interp dom w) (size dom) W) σ = _
  rw [Term.eval_rename_nil, Term.toFactor_op]
  show w (Table.toFactor (size dom)
      ((Term.val 3 Dom.U : Term Dom Fn).eval (interp dom w) (size dom) W) σ)
    (Table.toFactor (size dom)
      ((Term.val 2 Dom.R : Term Dom Fn).eval (interp dom w) (size dom) W) σ) = _
  rw [Term.toFactor_val, Term.toFactor_val]
  rfl

/-- The belief after the first choice has no variables: the referent is chosen uniformly. -/
theorem vars_prior : (prior dom w).vars = [] := rfl

theorem prior_nonneg : 0 ≤ Table.toFactor (size dom) (prior dom w) :=
  Term.chooses_nonneg (W := #[.const 1, weight₁ dom w]) (size := size dom) (arith dom w) 0 2
    (.ref 1)
    (fun σ ↦ by
      show (0 : ℝ) ≤ Table.toFactor (size dom) (.const 1) σ
      rw [Table.toFactor_const]
      exact zero_le_one)
    (fun σ ↦ by
      show (0 : ℝ) ≤ Table.toFactor (size dom)
        (one.eval (interp dom w) (size dom) #[.const 1]) σ
      rw [one_apply]
      exact zero_le_one)

variable (hw : ∀ a b, 0 ≤ w a b)
include hw

theorem weight₂_nonneg : 0 ≤ Table.toFactor (size dom) (weight₂ dom w) := fun σ ↦ by
  show (0 : ℝ) ≤ Table.toFactor (size dom)
    (said.eval (interp dom w) (size dom) #[.const 1, weight₁ dom w, prior dom w]) σ
  rw [said_apply]
  exact hw _ _

theorem joint_nonneg : 0 ≤ Table.toFactor (size dom) (joint dom w) :=
  Term.chooses_nonneg (W := tables₃ dom w) (size := size dom) (arith dom w) 2 3 (.ref 3)
    (prior_nonneg dom w) (weight₂_nonneg dom w hw)

/-- After the two choices of the speaker, the belief of the listener is the joint measure of the
referent and the utterance: the measure of the referent with the kernel of the speaker, whose
weight is the table `3`. -/
theorem measure_joint (σ : ∀ i, Fin (size dom i)) :
    (Table.toBelief (size dom) ({2} ∪ {3}) (joint dom w)).toNNReal.measure σ =
      ((Table.toBelief (size dom) {2} (prior dom w)).toNNReal.measure σ ⊗ₘ
        Kernel.ofFunOfCountable fun τ ↦
          ((Belief.choice 3 fun σ ↦
              (Table.toFactor (size dom) (weight₂ dom w) σ).toNNReal).measure
            (Function.updateFinset σ {2} τ) :
            Measure (∀ j : ({3} : Finset ℕ), Fin (size dom j)))).map
        (Equiv.piFinsetUnion (fun i ↦ Fin (size dom i))
          (Finset.disjoint_singleton_right.2 (by decide : (3 : ℕ) ∉ ({2} : Finset ℕ)))) :=
  Term.measure_chooses (W := tables₃ dom w) (size := size dom) (arith dom w) 2 {2} 3 (.ref 3)
    (prior_nonneg dom w) (weight₂_nonneg dom w hw) (by decide)
    (by show 3 ∉ (prior dom w).vars; rw [vars_prior]; simp) σ

/-- After the observation, the belief of the listener is the joint measure conditioned on the
utterance, as a measure on the referent. -/
theorem measure_posterior (σ : ∀ i, Fin (size dom i)) :
    (Table.toBelief (size dom) (({2} ∪ {3} : Finset ℕ).erase 3)
        (posterior dom w)).toNNReal.measure σ =
      (((Table.toBelief (size dom) ({2} ∪ {3}) (joint dom w)).toNNReal.measure σ)[|
          {τ | τ ⟨3, by simp⟩ = σ 3}]).map
        (Finset.restrict₂ (π := fun i ↦ Fin (size dom i))
          (Finset.erase_subset 3 ({2} ∪ {3} : Finset ℕ))) :=
  Term.measure_observes (W := tables₄ dom w) (size := size dom) (arith dom w) 4 ({2} ∪ {3}) 3
    [2] (List.nodup_singleton 2) (by decide) (joint_nonneg dom w hw) (by decide) σ

end

end Memo.Posterior
