/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fin.VecNotation

/-!
# The syntax of memo

This file defines the statements, expressions and models of memo.

A memo model describes agents who make choices and reason about each other. A statement says that
an agent chooses a value from a domain, with probability proportional to an expression; that an
agent observes a choice; that an agent knows a choice; or that an agent thinks, in which case the
statements inside it happen in that agent's model of the world. An expression is a number computed from choices: a choice of the
current agent, a query for the value that another agent computes, or the expectation of a value
that the current agent is uncertain of.

For example, the statement `listener: thinks[ speaker: chooses(r in R, wpp=1) ]` of memo is the
term `.thinks listener (.chooses speaker r R (.lit 1))`.

## Main definitions

* `Memo.Ref A`: the current agent `self`, or an agent with a name in `A`.
* `Memo.Expr A N D K`: the expressions, over names `A` of agents, `N` of choices and `D` of
  domains, with numbers in `K`.
* `Memo.Stmt A N D K`: the statements.
* `Memo.Expr.op₁ f e`, `Memo.Expr.op₂ f e₁ e₂`: an operator of one or two arguments applied.
* `Memo.Model A N D K`: a model, which has axes, a statement and an expression to return.

## Implementation notes

The constructors follow the grammar of the memo paper, with the statements `knows`, `observes_event` and `forgets_about` of memo and its `chooses` of
several values added.
Three forms of that grammar are not constructors. A parameter of a model is an argument of the Lean function that builds the model. A
reference to another model and the cost of a model are primitive operators, which is how the paper
gives their meaning. The expression `Pr[e]` of memo is `E[e]` for an `e` with values 0 and 1.

The numbers are in a type `K` and not in the real numbers, so that a model with rational numbers
can be evaluated.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

universe u v w x

namespace Memo

/-- A **reference to an agent** is the current agent, `self`, or an agent with a name. -/
inductive Ref (A : Type u) : Type u
  /-- The agent whose frame of mind is the current one. -/
  | self
  /-- The agent with the name `α`. -/
  | agent (α : A)
  deriving DecidableEq

mutual

/-- An **expression** of memo denotes a number that depends on choices. -/
inductive Expr (A : Type u) (N : Type v) (D : Type w) (K : Type x) : Type (max u v w x)
  /-- The numeric literal `r`. -/
  | lit (r : K)
  /-- The primitive operator `f` applied to the expressions `es`. -/
  | op {k : ℕ} (f : (Fin k → K) → K) (es : Fin k → Expr A N D K)
  /-- The choice `x` of the current agent. -/
  | choice (x : N)
  /-- The query `α[e]`: the value of `e` in the frame of mind of the agent `α`. -/
  | query (α : A) (e : Expr A N D K)
  /-- The expectation `E[e]` of `e` over the choices that the current agent is uncertain of. -/
  | expect (e : Expr A N D K)
  /-- The hypothetical `imagine[s, e]`: the value of `e` if the statement `s` were to happen. -/
  | imagine (s : Stmt A N D K) (e : Expr A N D K)

/-- A **statement** of memo changes the frames of mind of the agents. -/
inductive Stmt (A : Type u) (N : Type v) (D : Type w) (K : Type x) : Type (max u v w x)
  /-- The statement `α: chooses(x in X, wpp=e)`: the agent `α` chooses `x` from the domain `X`
  with probability proportional to `e`. -/
  | chooses (α : A) (x : N) (X : D) (e : Expr A N D K)
  /-- The statement `α: observes [β.x] is γ.y`: the agent `α` learns the choice `x` of `β`, whose
  value is the choice `y` of `γ`. -/
  | observes (α β : A) (x : N) (γ : Ref A) (y : N)
  /-- The statement `α: chooses(x in X, y in Y, wpp=e)`: the agent `α` chooses several values
  together, with probability proportional to `e`. -/
  | choosesMany (α : A) (xs : List (N × D)) (e : Expr A N D K)
  /-- The statement `α: chooses(x in X, to_maximize=e)`: the agent `α` chooses `x` from the domain
  `X` uniformly among the values at which `e` is greatest. -/
  | choosesMax (α : A) (x : N) (X : D) (e : Expr A N D K)
  /-- The statement `α: snapshots_self_as(β)`: the agent `α` gets a model of an agent `β` that is a
  copy of `α` as it is now. -/
  | snapshot (α β : A)
  /-- The statement `α: forgets_about(x, y)`: the agent `α` no longer has the choices `xs`, and
  the current agent no longer follows them. -/
  | forgets (α : A) (xs : List N)
  /-- The statement `α: observes_event(wpp=e)`: the agent `α` observes an event that happens with
  probability proportional to `e`. The statement `α: observes_that[e]` is the case in which `e`
  is one or zero. -/
  | observesEvent (α : A) (e : Expr A N D K)
  /-- The statement `α: knows(γ.y)`: the agent `α` knows the choice `y` of `γ`, without having
  observed it. -/
  | knows (α : A) (γ : Ref A) (y : N)
  /-- The statement `α: thinks[s]`: the statement `s` happens in the agent `α`'s model of the
  world. -/
  | thinks (α : A) (s : Stmt A N D K)
  /-- The statement `s₁; s₂`: `s₁` happens and then `s₂`. -/
  | seq (s₁ s₂ : Stmt A N D K)

end

@[inherit_doc] scoped infixr:60 " ;; " => Stmt.seq

variable {A : Type u} {N : Type v} {D : Type w} {K : Type x}

/-- The operator `f` of one argument applied to the expression `e`. -/
def Expr.op₁ (f : K → K) (e : Expr A N D K) : Expr A N D K := .op (fun v ↦ f (v 0)) ![e]

/-- The operator `f` of two arguments applied to the expressions `e₁` and `e₂`. -/
def Expr.op₂ (f : K → K → K) (e₁ e₂ : Expr A N D K) : Expr A N D K :=
  .op (fun v ↦ f (v 0) (v 1)) ![e₁, e₂]

/-- A **model** has axes, each a name with a domain, a statement, and an expression to return. Its
value is an array with one entry for each choice of a value on every axis. -/
structure Model (A : Type u) (N : Type v) (D : Type w) (K : Type x) where
  /-- The axes of the array that the model returns. -/
  axes : List (N × D)
  /-- The statement of the model. -/
  body : Stmt A N D K
  /-- The expression that the model returns. -/
  ret : Expr A N D K

end Memo
