/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Core.Table
public import Mathlib.Algebra.Field.Defs

/-!
# Programs on tables

This file defines the arithmetic that a memo model asks for, with the names of the model removed.

Every choice of the model has a number, and every agent's model of the world, at any depth, has a
number: its mind. Each mind has a table, the probability of the choices that the mind is uncertain
of given the others. A term denotes a table. A step changes the table of one mind. A program is a
list of steps and a term for the array to return.

For example, the model in which a speaker chooses one of three referents with equal weight, and
which returns the probability of each, is the step `.chooses 0 [(1, 3)] (.lit 1)`, which multiplies the
table of the mind `0` by a third along the choice `1`, and the term
`.expect 0 [(1, 3)] (.op _ ![.val 1 3 _, .val 0 3 _])`.

## Main definitions

* `Memo.Core.Term K`: a number, an operator applied to terms, the value of a choice, an
  expectation in a mind, or a term read at other choices.
* `Memo.Core.Step K`: a choice, a weight or an observation in a mind.
* `Memo.Core.Program K`: a number of minds, a list of steps, a term and the axes of the array.
* `Memo.Core.Term.eval W t`: the table of the term `t`, when `W` holds the tables of the minds.
* `Memo.Core.Step.run W s`: the tables of the minds after the step `s`.
* `Memo.Core.Program.entries p`: the entries of the array of the program `p`, in row-major order.
-/

@[expose] public section

universe u

namespace Memo.Core

/-- A **term** denotes a table of numbers that depends on choices. -/
inductive Term (K : Type u) : Type u
  /-- The number `r`. -/
  | lit (r : K)
  /-- The operator `f` applied to the terms `ts`. -/
  | op {k : ℕ} (f : (Fin k → K) → K) (ts : Fin k → Term K)
  /-- The value of the choice `i`, which has `size` values: the number `v j` at the position
  `j`. -/
  | val (i size : ℕ) (v : ℕ → K)
  /-- The expectation of `t` in the mind `m`: the sum of `t` times the table of `m` over the
  choices in `over`, each given with its size. -/
  | expect (m : ℕ) (over : List (ℕ × ℕ)) (t : Term K)
  /-- The term `t` read at other choices: each choice `i` with a pair `(i, j)` in `links` is
  replaced by `j`. -/
  | rename (links : List (ℕ × ℕ)) (t : Term K)
  /-- The number one where `t` is greatest along the choice `i`, which has `size` values, and
  zero elsewhere. -/
  | best (i size : ℕ) (t : Term K)

/-- A **step** changes the table of one mind. -/
inductive Step (K : Type u) : Type u
  /-- The choices in `over`, each given with its size, are made together with weight `t`: the
  table of the mind `m` is multiplied by `t` divided by its sum over them. -/
  | chooses (m : ℕ) (over : List (ℕ × ℕ)) (t : Term K)
  /-- The table of the mind `m` is multiplied by `t`. -/
  | weighs (m : ℕ) (t : Term K)
  /-- A choice is observed in the mind `m`: its table is divided by its sum over the choices in
  `over`, the ones that remain uncertain. -/
  | observes (m : ℕ) (over : List (ℕ × ℕ))

/-- A **program** has a number of minds, a list of steps, a term for the array to return, and the
axes of that array: choices with their sizes. -/
structure Program (K : Type u) : Type u where
  /-- The number of minds. -/
  minds : ℕ
  /-- The steps, in order. -/
  steps : List (Step K)
  /-- The term for the array that the program returns. -/
  ret : Term K
  /-- The choices that are the axes of the array, each with its size. -/
  axes : List (ℕ × ℕ)

variable {K : Type u} [Semifield K] [LinearOrder K]

/-- The **table of a term**, when `W` holds the table of every mind. -/
def Term.eval (W : Array (Table K)) : Term K → Table K
  | .lit r => .const r
  | .op f ts =>
    let tables := Array.ofFn fun i ↦ (ts i).eval W
    .op f fun i ↦ tables.getD i (.const 0)
  | .val i size v => .ofFn [(i, size)] fun σ ↦ v (σ i)
  | .expect m over t => (t.eval W * W.getD m (.const 1)).sumOver over
  | .rename links t => (t.eval W).rename links
  | .best i size t => (t.eval W).best i size

/-- The tables of the minds after a step. -/
def Step.run (W : Array (Table K)) : Step K → Array (Table K)
  | .chooses m over t =>
    let w := t.eval W
    W.setIfInBounds m (W.getD m (.const 1) * (w / w.sumOver over))
  | .weighs m t => W.setIfInBounds m (W.getD m (.const 1) * t.eval W)
  | .observes m over =>
    let w := W.getD m (.const 1)
    W.setIfInBounds m (w / w.sumOver over)

/-- The table that a program returns: the table of its term after its steps, when every mind
starts with the table of the number one. -/
def Program.table (p : Program K) : Table K :=
  p.ret.eval (p.steps.foldl Step.run (Array.replicate p.minds (.const 1)))

/-- The entries of the array of a program, in row-major order. -/
def Program.entries (p : Program K) : List K :=
  let t := p.table
  (Table.ofFn p.axes fun σ ↦ t.get σ).data.toList

end Memo.Core
