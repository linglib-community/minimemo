/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Model
public import Minimemo.Bridge.Measure
public import Minimemo.Example.NaiveListener

/-!
# The belief of a listener is a posterior

This file takes a listener with any utterances, any referents and any speaker, with real numbers,
and proves from the program of the model that the belief of the listener is the posterior of
probability theory.

A listener thinks that a speaker chooses a referent uniformly and then an utterance with weight
`w u r`, and observes the utterance. The program of this model adds five tables. After the two
choices, the belief of the listener is the joint measure of the referent and the utterance: the
measure of the referent with the kernel of the speaker. After the observation it is that joint measure
conditioned on the utterance, as a measure on the referent.

Nothing is evaluated: the domains and the weight are arbitrary, and the results follow from the
theorems about steps.

## Main definitions

* `Memo.Posterior.model`: the model.
* `Memo.Posterior.interp dom w`: its interpretation, with any domains and any weight `w`.
* `Memo.Posterior.thinks dom w`, `Memo.Posterior.observes dom w`: the tables after the listener
  thinks about the speaker, and after the listener observes the utterance.

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
open scoped NNReal

namespace Memo.Posterior

open NaiveListener (Agent Name Dom)

noncomputable section

variable (dom : Dom → Domain ℝ≥0) (w : ℝ≥0 → ℝ≥0 → ℝ≥0)

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

/-- The interpretation of the model: any domains, the weight `w`, and the literal one. -/
def interp : Interp Dom Fn ℝ≥0 where
  dom := dom
  op {k} o := match k, o with
    | _, .inr .w => fun v ↦ w (v 0) (v 1)
    | _, .inl .mul => fun v ↦ v 0 * v 1
    | _, .inl .div => fun v ↦ v 0 / v 1
    | _, .inl _ => fun _ ↦ 0
  lit q := (q : ℝ).toNNReal

/-- The sizes of the choices of the model: the axes `0` and `1`, and the referent `2` and the
utterance `3` that the listener thinks the speaker chooses. -/
def size (i : ℕ) : ℕ :=
  ([(dom .U).size, (dom .R).size, (dom .R).size, (dom .U).size] : List ℕ).getD i 0

theorem arith : (interp dom w).Arith := ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The terms of the tables of the program of the model. -/
def steps : List (Term Dom Fn) := ((Model.program model).map (·.steps)).getD []

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

theorem doms_eq : (Model.program model).map (·.doms) = some [.U, .R, .R, .U] := rfl

/-- The tables `0` to `3`: after the listener thinks that the speaker chooses the referent, with
the weight of the utterance. -/
def prior : Array (Table ℝ≥0) :=
  let W₁ := #[.const 1].push (one.eval (interp dom w) (size dom) #[.const 1])
  let W₂ := W₁.push ((Term.chooses 0 [2] (.ref 1) : Term Dom Fn).eval (interp dom w) (size dom) W₁)
  W₂.push (said.eval (interp dom w) (size dom) W₂)

/-- The tables `0` to `4`: after the listener thinks that the speaker chooses the utterance. -/
def thinks : Array (Table ℝ≥0) :=
  (prior dom w).push
    ((Term.chooses 2 [3] (.ref 3) : Term Dom Fn).eval (interp dom w) (size dom) (prior dom w))

/-- The table after the listener observes the utterance. -/
def observes : Table ℝ≥0 :=
  (Term.observes 4 [2] : Term Dom Fn).eval (interp dom w) (size dom) (thinks dom w)

/-- The table that the program returns is computed from these tables. -/
theorem table_eq (p : Program Dom Fn) (hp : Model.program model = some p) :
    p.steps.foldl (fun W t ↦ W.push (t.eval (interp dom w) (size dom) W)) #[.const 1] =
      (thinks dom w).push (observes dom w) := by
  obtain rfl := Option.some.inj hp
  rfl

/-- The weight of the utterance in the program is `w` at the values of the utterance and of the
referent. -/
theorem said_apply (W : Array (Table ℝ≥0)) (σ : ∀ i, Fin (size dom i)) :
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
theorem vars_prior : ((prior dom w).getD 2 (.const 1)).vars = [] := rfl

/-- After the two choices of the speaker, the belief of the listener is the joint measure of the
referent and the utterance: the measure of the referent with the kernel of the speaker. -/
theorem measure_joint (σ : ∀ i, Fin (size dom i)) :
    (Table.toBelief (size dom) ({2} ∪ {3}) ((thinks dom w).getD 4 (.const 1))).measure σ =
      ((Table.toBelief (size dom) {2} ((prior dom w).getD 2 (.const 1))).measure σ ⊗ₘ
        Kernel.ofFunOfCountable fun τ ↦
          ((Belief.choice 3 (Table.toFactor (size dom)
            ((Term.ref 3 : Term Dom Fn).eval (interp dom w) (size dom) (prior dom w)))).measure
              (Function.updateFinset σ {2} τ) :
            Measure (∀ j : ({3} : Finset ℕ), Fin (size dom j)))).map
        (Equiv.piFinsetUnion (fun i ↦ Fin (size dom i))
          (Finset.disjoint_singleton_right.2 (by decide : (3 : ℕ) ∉ ({2} : Finset ℕ)))) :=
  Term.measure_chooses (W := prior dom w) (size := size dom) (arith dom w) 2 {2} 3 (.ref 3)
    (by decide) (by rw [vars_prior]; simp) σ

/-- The weight in that kernel is the weight of the utterance, `w`. -/
theorem ref_said (σ : ∀ i, Fin (size dom i)) :
    Table.toFactor (size dom)
        ((Term.ref 3 : Term Dom Fn).eval (interp dom w) (size dom) (prior dom w)) σ =
      w ((dom .U).val (σ 3)) ((dom .R).val (σ 2)) :=
  said_apply dom w _ σ

/-- After the observation, the belief of the listener is the joint measure conditioned on the
utterance, as a measure on the referent. -/
theorem measure_posterior (σ : ∀ i, Fin (size dom i)) :
    (Table.toBelief (size dom) (({2} ∪ {3} : Finset ℕ).erase 3) (observes dom w)).measure σ =
      (((Table.toBelief (size dom) ({2} ∪ {3}) ((thinks dom w).getD 4 (.const 1))).measure σ)[|
          {τ | τ ⟨3, by simp⟩ = σ 3}]).map
        (Finset.restrict₂ (π := fun i ↦ Fin (size dom i))
          (Finset.erase_subset 3 ({2} ∪ {3} : Finset ℕ))) :=
  Term.measure_observes (W := thinks dom w) (size := size dom) (arith dom w) 4 ({2} ∪ {3}) 3 [2]
    (List.nodup_singleton 2) (by decide) (by decide) σ

end

end Memo.Posterior
