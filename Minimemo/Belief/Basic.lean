/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

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

* `Memo.Factor X K`: the type `(∀ i, X i) → K` of factors.
* `Memo.Factor.sumOver s f`: the sum of `f` over the values of the choices in `s`.
* `Memo.Belief X K`: a set of uncertain choices with a factor.
* `Memo.Belief.chooses b i w`: the belief after the choice `i` with weight `w`.
* `Memo.Belief.choice i w`: the belief in which only the choice `i` is uncertain, with weight
  `w`.
* `Memo.Belief.observes b i`: the belief after the choice `i` is observed.
* `Memo.Belief.expect b e`: the expectation of the factor `e`.
* `Memo.Belief.IsNormalized b`: at every assignment, the factor of `b` sums to one or to zero
  over the uncertain choices.

## Main results

* `Memo.Factor.sumOver_union`: the sum over a union of two disjoint sets of choices is the
  sum over one of the sum over the other.
* `Memo.Belief.observes_isNormalized`: the belief after an observation is normalized.
* `Memo.Belief.chooses_mul_left`: a weight matters only up to a nonzero factor.
* `Memo.Belief.IsNormalized.chooses`: the belief after a choice is normalized, if the belief
  before it is, its factor does not depend on the new choice, and the weight has a nonzero sum
  over that choice.
-/

@[expose] public section

namespace Memo

variable {ι : Type*} [DecidableEq ι] (X : ι → Type*) (K : Type*)

/-- A **factor** is a number that depends on the assignment of a value to every choice. -/
abbrev Factor := (∀ i, X i) → K

variable {X K} [∀ i, Fintype (X i)] [Semifield K]

/-- The **sum of a factor over a set of choices** adds its values at the assignments that agree
with the given one off that set. -/
def Factor.sumOver (s : Finset ι) (f : Factor X K) : Factor X K :=
  fun σ ↦ ∑ τ : ∀ i : s, X i, f (Function.updateFinset σ s τ)

omit [∀ i, Fintype (X i)] in
theorem Function.updateFinset_updateFinset_self (σ : ∀ i, X i) (s : Finset ι)
    (τ τ' : ∀ i : s, X i) :
    Function.updateFinset (Function.updateFinset σ s τ) s τ' = Function.updateFinset σ s τ' := by
  funext j
  by_cases h : j ∈ s <;> simp [Function.updateFinset, h]

/-- The sum of a factor over a set of choices does not depend on the values of those choices. -/
theorem Factor.sumOver_updateFinset (s : Finset ι) (f : Factor X K) (σ : ∀ i, X i)
    (τ : ∀ i : s, X i) : f.sumOver s (Function.updateFinset σ s τ) = f.sumOver s σ := by
  simp only [Factor.sumOver, Function.updateFinset_updateFinset_self]

/-- The sum over a union of two disjoint sets of choices is the sum over one of the sum over the
other. -/
theorem Factor.sumOver_union {s t : Finset ι} (hst : Disjoint s t) (f : Factor X K) :
    f.sumOver (s ∪ t) = (f.sumOver t).sumOver s := by
  funext σ
  simp only [Factor.sumOver, Function.updateFinset_updateFinset hst]
  rw [← (Equiv.piFinsetUnion X hst).sum_comp, Fintype.sum_prod_type]

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
  uncertain := b.uncertain ∪ {i}
  weight := b.weight * (w / w.sumOver {i})

/-- The belief in which only the choice `i` is uncertain, with the weight `w` divided by its sum
over `i`: the probability of each value of the choice. -/
abbrev choice (i : ι) (w : Factor X K) : Belief X K where
  uncertain := {i}
  weight := w / w.sumOver {i}

/-- The belief after the choice `i` is **observed**: the choice becomes certain, and the factor is
divided by its sum over the choices that remain uncertain. -/
def observes (b : Belief X K) (i : ι) : Belief X K where
  uncertain := b.uncertain.erase i
  weight := b.weight / b.weight.sumOver (b.uncertain.erase i)

/-- The **expectation** of a factor in a belief is the sum, over the uncertain choices, of the
factor times the factor of the belief. -/
def expect (b : Belief X K) (e : Factor X K) : Factor X K := (e * b.weight).sumOver b.uncertain

/-- A weight matters only up to a nonzero factor: the choice with weight `c * w` gives the same
belief as the choice with weight `w`. -/
theorem chooses_mul_left {c : K} (hc : c ≠ 0) (b : Belief X K) (i : ι) (w : Factor X K) :
    b.chooses i (fun σ ↦ c * w σ) = b.chooses i w := by
  unfold chooses
  congr 2
  funext σ
  simp only [Pi.div_apply, Factor.sumOver, ← Finset.mul_sum, mul_div_mul_left _ _ hc]

/-- The belief after an observation is normalized. -/
theorem observes_isNormalized (b : Belief X K) (i : ι) : (b.observes i).IsNormalized := by
  intro σ
  have h : ∀ τ : ∀ j : (b.uncertain.erase i), X j,
      b.weight.sumOver (b.uncertain.erase i) (Function.updateFinset σ _ τ) =
        b.weight.sumOver (b.uncertain.erase i) σ := fun τ ↦ Factor.sumOver_updateFinset _ _ _ _
  simp only [observes, Factor.sumOver, Pi.div_apply] at h ⊢
  simp only [h, ← Finset.sum_div]
  by_cases h0 : (∑ τ : ∀ j : (b.uncertain.erase i), X j,
      b.weight (Function.updateFinset σ _ τ)) = 0
  · exact .inr (by rw [h0, div_zero])
  · exact .inl (div_self h0)

/-- The belief after a choice is normalized, if the belief before it is, its factor does not
depend on the new choice, and the weight has a nonzero sum over that choice. -/
theorem IsNormalized.chooses {b : Belief X K} {i : ι} {w : Factor X K} (hb : b.IsNormalized)
    (hi : i ∉ b.uncertain)
    (hbi : ∀ σ (τ : ∀ j : ({i} : Finset ι), X j),
      b.weight (Function.updateFinset σ {i} τ) = b.weight σ)
    (hw : ∀ σ, w.sumOver {i} σ ≠ 0) : (b.chooses i w).IsNormalized := by
  have inner : (b.weight * (w / w.sumOver {i})).sumOver {i} = b.weight := by
    funext σ
    have hZ : ∀ τ : ∀ j : ({i} : Finset ι), X j,
        w.sumOver {i} (Function.updateFinset σ {i} τ) = w.sumOver {i} σ :=
      fun τ ↦ Factor.sumOver_updateFinset _ _ _ _
    have h0 := hw σ
    simp only [Factor.sumOver, Pi.mul_apply, Pi.div_apply] at hZ h0 ⊢
    simp only [hbi, hZ, ← Finset.mul_sum, ← Finset.sum_div]
    rw [div_self h0, mul_one]
  intro σ
  have hd : Disjoint b.uncertain {i} := Finset.disjoint_singleton_right.2 hi
  simp only [Belief.chooses, Factor.sumOver_union hd, inner]
  exact hb σ

end Belief

end Memo
