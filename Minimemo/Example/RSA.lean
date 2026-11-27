/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Belief
public import Mathlib.Tactic.NormNum

/-!
# The Rational Speech Acts model

This file writes the first model of the memo paper with the operations on tables, and checks it
against the array that the paper prints.

There are three referents, a green square, a green circle and a pink circle, and four utterances,
*green*, *pink*, *square* and *round*. A listener thinks that a speaker chooses a referent
uniformly and then an utterance with weight `w r u`. The listener observes the utterance and
chooses a referent with weight equal to its probability that the speaker chose that referent. The
model returns the probability that the listener chooses each referent.

## Main definitions

* `Memo.RSA.speakerModel w`: the listener's table after the two choices of the speaker.
* `Memo.RSA.listenerBelief w`: the listener's table after it observes the utterance.
* `Memo.RSA.listener w`: the value the model returns at each utterance and referent.
* `Memo.RSA.naive`: the weights of a speaker who chooses uniformly among the true utterances.

## Main results

* `Memo.RSA.listener_naive`: with the naive weights the model returns the array that the paper
  prints for the naive listener.
-/

@[expose] public section

open scoped NNReal

namespace Memo.RSA

/-- The utterances of the model. -/
inductive Utterance
  | green | pink | square | round
  deriving DecidableEq

instance : Fintype Utterance :=
  ⟨{.green, .pink, .square, .round}, fun u ↦ by cases u <;> simp⟩

/-- The referents of the model. -/
inductive Referent
  | greenSquare | greenCircle | pinkCircle
  deriving DecidableEq

instance : Fintype Referent :=
  ⟨{.greenSquare, .greenCircle, .pinkCircle}, fun r ↦ by cases r <;> simp⟩

/-- An utterance **denotes** a referent if it names its colour or its shape. -/
def Denotes (u : Utterance) (r : Referent) : Prop :=
  (u, r) ∈ [(Utterance.green, Referent.greenSquare), (.green, .greenCircle), (.pink, .pinkCircle),
    (.square, .greenSquare), (.round, .greenCircle), (.round, .pinkCircle)]

instance : DecidableRel Denotes := fun _ _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- The listener's table after `speaker: chooses(r in R, wpp=1)` and
`speaker: chooses(u in U, wpp=w r u)`. Nothing is known, and the referent and the utterance are
uncertain. -/
noncomputable def speakerModel (w : Referent → Utterance → ℝ≥0) :
    Table Unit (Referent × Utterance) :=
  (Table.normalize fun _ _ ↦ 1 : Table Unit Referent).chooses fun (_, r) u ↦ w r u

/-- The listener's table after `listener: observes [speaker.u] is u`. The utterance is known and
the referent is uncertain. -/
noncomputable def listenerBelief (w : Referent → Utterance → ℝ≥0) :
    Table (Unit × Utterance) Referent :=
  (speakerModel w).observes

/-- The value of the model: after `listener: chooses(r in R, wpp=Pr[speaker.r == r])`, the
probability `Pr[listener.r == r]` in the frame of the observer, who knows the utterance. -/
noncomputable def listener (w : Referent → Utterance → ℝ≥0) (u : Utterance) (r : Referent) : ℝ :=
  (Table.normalize fun u r' ↦ listenerBelief w ((), u) r').expect
    (fun _ r' ↦ if r' = r then 1 else 0) u

/-- The weights of a speaker who chooses uniformly among the utterances that denote the
referent. -/
def naive (r : Referent) (u : Utterance) : ℝ≥0 := if Denotes u r then 1 else 0

theorem sum_referent {M : Type*} [AddCommMonoid M] (f : Referent → M) :
    ∑ r, f r = f .greenSquare + f .greenCircle + f .pinkCircle := by
  simp [Finset.univ, Fintype.elems, Finset.sum_insert, add_assoc]

theorem sum_utterance {M : Type*} [AddCommMonoid M] (f : Utterance → M) :
    ∑ u, f u = f .green + f .pink + f .square + f .round := by
  simp [Finset.univ, Fintype.elems, Finset.sum_insert, add_assoc]

/-- With the naive weights the model returns the array that the paper prints for the naive
listener: *green* and *round* leave two referents equally likely, and *pink* and *square* pick
out one. -/
theorem listener_naive (u : Utterance) (r : Referent) :
    listener naive u r =
      if Denotes u r then (if u = .green ∨ u = .round then 1 / 2 else 1) else 0 := by
  cases u <;> cases r <;>
    simp only [listener, listenerBelief, speakerModel, Table.expect, Table.normalize_apply,
      Table.observes_apply, Table.chooses_apply, sum_referent, sum_utterance] <;>
    simp [naive, Denotes] <;>
    norm_num

end Memo.RSA
