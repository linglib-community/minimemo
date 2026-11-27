/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Fintype.Pi

/-!
# Beliefs over a family of choices

This file defines the tables of memo without names or axes.

The choices of a model are indexed by a type `ι`, and the choice `i` has values in `X i`. An
assignment gives every choice a value. A factor is a number that depends on the assignment. A
belief of an agent is a set of choices that the agent is uncertain of, with a factor: the
probability of the uncertain choices given the others.

The statements of memo act on a belief as follows. A choice multiplies the factor by a weight
divided by its sum over the new choice, and makes that choice uncertain. An observation makes a
choice certain and divides the factor by its sum over the choices that remain uncertain. An
expectation is the sum, over the uncertain choices, of a factor times the factor of the belief.

## Main definitions

* `Memo.Core.Factor X K`: the type `(∀ i, X i) → K` of factors.
* `Memo.Core.Factor.sumOver s f`: the sum of `f` over the values of the choices in `s`.
* `Memo.Core.Belief X K`: a set of uncertain choices with a factor.
* `Memo.Core.Belief.chooses b i w`: the belief after the choice `i` with weight `w`.
* `Memo.Core.Belief.observes b i`: the belief after the choice `i` is observed.
* `Memo.Core.Belief.expect b e`: the expectation of the factor `e`.
* `Memo.Core.Belief.IsNormalized b`: at every assignment, the factor of `b` sums to one or to zero
  over the uncertain choices.

## TODO

A choice with a nonnegative weight and an observation each take a normalized belief to a
normalized belief, when the factor of the belief does not depend on the new choice. These are not
proved here.
-/

@[expose] public section

namespace Memo.Core

variable {ι : Type*} [DecidableEq ι] (X : ι → Type*) (K : Type*)

/-- A **factor** is a number that depends on the assignment of a value to every choice. -/
abbrev Factor := (∀ i, X i) → K

variable {X K} [∀ i, Fintype (X i)] [Semifield K]

/-- The **sum of a factor over a set of choices** adds its values at the assignments that agree
with the given one off that set. -/
def Factor.sumOver (s : Finset ι) (f : Factor X K) : Factor X K :=
  fun σ ↦ ∑ τ : ∀ i : s, X i, f (Function.updateFinset σ s τ)

variable (X K) in
/-- A **belief** is a set of choices that an agent is uncertain of, with a factor: the probability
of the uncertain choices given the others. -/
structure Belief where
  /-- The choices that the agent is uncertain of. -/
  uncertain : Finset ι
  /-- The probability of the uncertain choices given the others. -/
  weight : Factor X K

namespace Belief

/-- A belief **is normalized** if, at every assignment, its factor sums to one or to zero over the
uncertain choices. -/
def IsNormalized (b : Belief X K) : Prop :=
  ∀ σ, b.weight.sumOver b.uncertain σ = 1 ∨ b.weight.sumOver b.uncertain σ = 0

/-- The belief after a **choice** `i` with weight `w`: the choice becomes uncertain, and the factor
is multiplied by `w` divided by its sum over `i`. -/
def chooses (b : Belief X K) (i : ι) (w : Factor X K) : Belief X K where
  uncertain := insert i b.uncertain
  weight := b.weight * (w / w.sumOver {i})

/-- The belief after the choice `i` is **observed**: the choice becomes certain, and the factor is
divided by its sum over the choices that remain uncertain. -/
def observes (b : Belief X K) (i : ι) : Belief X K where
  uncertain := b.uncertain.erase i
  weight := b.weight / b.weight.sumOver (b.uncertain.erase i)

/-- The **expectation** of a factor in a belief is the sum, over the uncertain choices, of the
factor times the factor of the belief. -/
def expect (b : Belief X K) (e : Factor X K) : Factor X K := (e * b.weight).sumOver b.uncertain

end Belief

end Memo.Core
