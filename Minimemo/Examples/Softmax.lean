/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Theory.Unfold
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A choice by softmax

An agent chooses among `n` options with weight the exponential of `β` times the utility of the
option, and the model returns the probability of each option. This file proves, from the program
of the model, that the probability of an option is the softmax of the scaled utilities.

## Main definitions

* `Memo.Softmax.model`: the model, as a memo program.

## Main results

* `Memo.Softmax.denote_program`: the model returns `exp (β * u x) / ∑ y, exp (β * u y)` at the
  option `x`.
* `Memo.Softmax.get_table`: the stored table of the model has that number.

## Implementation notes

The utility, the exponential and `β` are outside functions, so the result holds for every utility
and every real `β`. The proof names the meaning of each table of the program with `memo_unfold`
and simplifies.
-/

@[expose] public section

namespace Memo.Softmax

inductive Agent | alice deriving DecidableEq
inductive Name | x | pick deriving DecidableEq
inductive Dom | X deriving DecidableEq
inductive Fn : ℕ → Type
  | utility : Fn 1
  | exp : Fn 1
  | beta : Fn 0

/-- `alice: chooses(pick in X, wpp=exp(beta * utility(pick)))`, `return Pr[alice.pick == x]` -/
def model : Model Agent Name Dom Fn where
  axes := [(.x, .X)]
  body := .chooses .alice .pick .X
    (.call .exp ![.prim .mul ![.call .beta ![], .call .utility ![.choice .pick]]])
  ret := .expect (.prim .eq ![.query .alice (.choice .pick), .choice .x])

def dom (n : ℕ) : Dom → Domain ℝ := fun _ ↦ ⟨n, fun j ↦ j⟩

noncomputable def call (β : ℝ) (u : ℝ → ℝ) : {k : ℕ} → Fn k → (Fin k → ℝ) → ℝ
  | _, .utility, v => u (v 0)
  | _, .exp, v => Real.exp (v 0)
  | _, .beta, _ => β

def program : Program Dom Fn :=
  ⟨[.X, .X],
   [.rename [] (.app (.inr .exp) [.app (.inl .mul) [.app (.inr .beta) [],
      .app (.inr .utility) [.val 1 .X]]]),
    Term.chooses 0 [1] (.ref 1)],
   Term.expect 2 [1] (.app (.inl .eq) [.rename [] (.val 1 .X), .val 0 .X]), [0]⟩

theorem program_eq : Model.program model = .ok program := rfl

/-- The sizes of the choices: the axis and the choice of the agent. -/
def size (n : ℕ) (i : ℕ) : ℕ := ([n, n] : List ℕ).getD i 1

theorem denote_program (n : ℕ) (β : ℝ) (u : ℝ → ℝ) (σ : ℕ → ℕ) (h : σ 0 < n) :
    program.term.denote (.ofField (dom n) (call β u)) (size n) [fun _ ↦ 1] σ =
      Real.exp (β * u (σ 0)) / ∑ j ∈ Finset.range n, Real.exp (β * u j) := by
  memo_unfold [program, call, dom]
  rename_i f1 f2 h1 h2
  simp only [h2, h1, size, List.getD_cons_zero, List.getD_cons_succ, Function.update, Nat.cast_inj,
    one_mul, ite_mul, zero_mul, ↓reduceDIte]
  simp [Finset.sum_ite_eq', h]

/-- The stored table of the model has the softmax of the scaled utilities. -/
theorem get_table (n : ℕ) (β : ℝ) (u : ℝ → ℝ) (σ : ℕ → ℕ) (hσ : InRange (size n) σ) :
    (program.term.eval (.ofField (dom n) (call β u)) (size n) #[.const 1]).get (size n) σ =
      Real.exp (β * u (σ 0)) / ∑ j ∈ Finset.range n, Real.exp (β * u j) :=
  (Term.get_eval program.term _ _ Env.one σ hσ).trans (denote_program n β u σ (hσ 0))

end Memo.Softmax
