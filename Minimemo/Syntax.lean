/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Rat.Init

/-!
# The syntax of memo

This file defines the statements, expressions and models of memo.

A memo model describes agents who make choices and reason about each other. A statement says that
an agent chooses a value from a domain, with probability proportional to an expression; that an
agent observes a choice; that an agent knows a choice; or that an agent thinks, in which case the
statements inside it happen in that agent's model of the world. An expression is a number computed
from choices: a choice of the current agent, a query for the value that another agent computes, or
the expectation of a value that the current agent is uncertain of.

The syntax has no numbers but rational literals. An operator is a name: one of the operators of
memo, `Memo.Prim`, or a function that the model takes from outside, with a name in `F`. What the
names mean in a field of numbers is given apart from the model, so one model can be evaluated with
rational numbers and reasoned about with real numbers.

For example, the statement `listener: thinks[ speaker: chooses(r in R, wpp=1) ]` of memo is the
term `.thinks listener (.chooses speaker r R (.lit 1))`.

## Main definitions

* `Memo.Ref A`: the current agent `self`, or an agent with a name in `A`.
* `Memo.Prim k`: the operators of memo with `k` arguments.
* `Memo.Expr A N D F`: the expressions, over names `A` of agents, `N` of choices, `D` of domains
  and `F` of outside functions.
* `Memo.Stmt A N D F`: the statements.
* `Memo.Model A N D F`: a model, which has axes, a statement and an expression to return.

## Implementation notes

The constructors follow the grammar of the memo paper, with the statements `knows`,
`observes_event` and `forgets_about` of memo and its `chooses` of several values added. A
parameter of a model is an argument of the Lean function that builds the model. A reference to
another model is an outside function. The expression `Pr[e]` of memo is `E[e]` for an `e` with
values 0 and 1.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

universe u

namespace Memo

/-- A **reference to an agent** is the current agent, `self`, or an agent with a name. -/
inductive Ref (A : Type u) : Type u
  /-- The agent whose frame of mind is the current one. -/
  | self
  /-- The agent with the name `α`. -/
  | agent (α : A)
  deriving DecidableEq, Repr

/-- The **operators of memo that leave the rational numbers**: the exponential, the logarithm and
the power with any exponent. A model uses them as outside functions, with their meaning in the
real numbers or in floating point. -/
inductive Exp : ℕ → Type
  | exp : Exp 1
  | log : Exp 1
  /-- The power `a ** b`. -/
  | rpow : Exp 2
  deriving DecidableEq, Repr

/-- The **operators** of memo, by their number of arguments. A test has the value one when it
holds and zero when it does not, and a number is taken as true when it is not zero. -/
inductive Prim : ℕ → Type
  | add : Prim 2
  | sub : Prim 2
  | mul : Prim 2
  | div : Prim 2
  /-- The test `a == b`. -/
  | eq : Prim 2
  /-- The test `a != b`. -/
  | ne : Prim 2
  /-- The test `a < b`. -/
  | lt : Prim 2
  /-- The test `a <= b`. -/
  | le : Prim 2
  /-- The test `a and b`. -/
  | both : Prim 2
  /-- The test `a or b`. -/
  | either : Prim 2
  | neg : Prim 1
  | abs : Prim 1
  /-- The test that `a` is not zero. -/
  | truthy : Prim 1
  /-- The power `a ** n`, for a natural number `n`. -/
  | pow (n : ℕ) : Prim 1
  /-- The choice `b if a else c`, with the arguments in the order `a`, `b`, `c`. -/
  | ite : Prim 3
  deriving DecidableEq

mutual

/-- An **expression** of memo denotes a number that depends on choices. -/
inductive Expr (A N D : Type u) (F : ℕ → Type u) : Type u
  /-- The numeric literal `q`. -/
  | lit (q : ℚ)
  /-- An operator of memo, or an outside function with the name `f`, applied to the expressions
  `es`. -/
  | op {k : ℕ} (o : Prim k ⊕ F k) (es : Fin k → Expr A N D F)
  /-- The choice `x` of the current agent. -/
  | choice (x : N)
  /-- The query `α[e]`: the value of `e` in the frame of mind of the agent `α`. -/
  | query (α : A) (e : Expr A N D F)
  /-- The expectation `E[e]` of `e` over the choices that the current agent is uncertain of. -/
  | expect (e : Expr A N D F)
  /-- The hypothetical `imagine[s, e]`: the value of `e` if the statement `s` were to happen. -/
  | imagine (s : Stmt A N D F) (e : Expr A N D F)

/-- A **statement** of memo changes the frames of mind of the agents. -/
inductive Stmt (A N D : Type u) (F : ℕ → Type u) : Type u
  /-- The statement `α: chooses(x in X, wpp=e)`: the agent `α` chooses `x` from the domain `X`
  with probability proportional to `e`. -/
  | chooses (α : A) (x : N) (X : D) (e : Expr A N D F)
  /-- The statement `α: observes [β.x] is γ.y`: the agent `α` learns the choice `x` of `β`, whose
  value is the choice `y` of `γ`. -/
  | observes (α β : A) (x : N) (γ : Ref A) (y : N)
  /-- The statement `α: chooses(x in X, y in Y, wpp=e)`: the agent `α` chooses several values
  together, with probability proportional to `e`. -/
  | choosesMany (α : A) (xs : List (N × D)) (e : Expr A N D F)
  /-- The statement `α: chooses(x in X, to_maximize=e)`: the agent `α` chooses `x` from the domain
  `X` uniformly among the values at which `e` is greatest. -/
  | choosesMax (α : A) (x : N) (X : D) (e : Expr A N D F)
  /-- The statement `α: snapshots_self_as(β)`: the agent `α` gets a model of an agent `β` that is a
  copy of `α` as it is now. With `.self` for `α`, the mind itself gets the copy: an agent who
  imagines its own future starts from one. -/
  | snapshot (α : Ref A) (β : A)
  /-- The statement `α: forgets_about(x, y)`: the agent `α` no longer has the choices `xs`, and
  the current agent no longer follows them. -/
  | forgets (α : A) (xs : List N)
  /-- The statement `α: observes_event(wpp=e)`: the agent `α` observes an event that happens with
  probability proportional to `e`. The statement `α: observes_that[e]` is the case in which `e`
  is one or zero. -/
  | observesEvent (α : A) (e : Expr A N D F)
  /-- The statement `α: knows(γ.y)`: the agent `α` knows the choice `y` of `γ`, without having
  observed it. -/
  | knows (α : A) (γ : Ref A) (y : N)
  /-- The statement `α: thinks[s]`: the statement `s` happens in the agent `α`'s model of the
  world. -/
  | thinks (α : A) (s : Stmt A N D F)
  /-- The statement `pass`: nothing happens. -/
  | pass
  /-- The statement `s₁; s₂`: `s₁` happens and then `s₂`. -/
  | seq (s₁ s₂ : Stmt A N D F)

end

@[inherit_doc] scoped infixr:60 " ;; " => Stmt.seq

variable {A N D : Type u} {F : ℕ → Type u}

/-- The operator `p` of memo applied to the expressions `es`. -/
abbrev Expr.prim {k : ℕ} (p : Prim k) (es : Fin k → Expr A N D F) : Expr A N D F :=
  .op (.inl p) es

/-- The outside function `f` applied to the expressions `es`. -/
abbrev Expr.call {k : ℕ} (f : F k) (es : Fin k → Expr A N D F) : Expr A N D F :=
  .op (.inr f) es

/-- A **model** has axes, each a name with a domain, a statement, and an expression to return. Its
value is an array with one entry for each choice of a value on every axis. -/
structure Model (A N D : Type u) (F : ℕ → Type u) where
  /-- The axes of the array that the model returns. -/
  axes : List (N × D)
  /-- The statement of the model. -/
  body : Stmt A N D F
  /-- The expression that the model returns. -/
  ret : Expr A N D F

end Memo
