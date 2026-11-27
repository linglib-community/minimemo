/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Table
public import Mathlib.Algebra.Field.Defs

/-!
# Programs on tables

This file defines the arithmetic that a memo model asks for, with the names of the model removed.

Every choice of the model has a number. The tables that the model computes are numbered in order.
The table `0` has the number one, and each step adds a table, computed from the earlier ones. The
belief of an agent at some moment, the probability of the choices that the agent is uncertain of
given the others, is one of these tables. A term denotes a table. A program is a list of steps
and a term for the array to return.

For example, the model in which a speaker chooses one of three referents with equal weight, and
which returns the probability of each, is the step `.chooses 0 [(1, 3)] (.lit 1)`, which adds the
table `1`, a third along the choice `1`, and the term
`.expect 1 [(1, 3)] (.op _ ![.val 1 3 _, .val 0 3 _])`.

## Main definitions

* `Memo.Term K`: a number, an operator applied to terms, the value of a choice, an
  expectation, a term read at other choices, or a term after a step.
* `Memo.Step K`: a choice, a weight, an observation or a forgetting.
* `Memo.Program K`: a list of steps, a term and the axes of the array.
* `Memo.Term.eval W t`: the table of the term `t`, when `W` holds the tables so far.
* `Memo.Step.table W s`: the table that the step `s` adds.
* `Memo.Step.run W s`: the tables after the step `s`.
* `Memo.Program.entries p`: the entries of the array of the program `p`, in row-major order.
* `Memo.Program.rows p`: the same entries, as rows along the last axis.
-/

@[expose] public section

universe u

namespace Memo

mutual

/-- A **term** denotes a table of numbers that depends on choices. -/
inductive Term (K : Type u) : Type u
  /-- The number `r`. -/
  | lit (r : K)
  /-- The operator `f` applied to the terms `ts`. -/
  | op {k : ℕ} (f : (Fin k → K) → K) (ts : Fin k → Term K)
  /-- The value of the choice `i`, which has `size` values: the number `v j` at the position
  `j`. -/
  | val (i size : ℕ) (v : ℕ → K)
  /-- The expectation of `t` in the belief `w`: the sum of `t` times the table `w` over the
  choices in `over`, each given with its size. -/
  | expect (w : ℕ) (over : List (ℕ × ℕ)) (t : Term K)
  /-- The term `t` read at other choices: each choice `i` with a pair `(i, j)` in `links` is
  replaced by `j`. -/
  | rename (links : List (ℕ × ℕ)) (t : Term K)
  /-- The number one where `t` is greatest along the choice `i`, which has `size` values, and
  zero elsewhere. -/
  | best (i size : ℕ) (t : Term K)
  /-- The term `t` if the step `s` were to happen. -/
  | after (s : Step K) (t : Term K)

/-- A **step** adds a table, computed from the tables so far. -/
inductive Step (K : Type u) : Type u
  /-- The choices in `over`, each given with its size, are made together with weight `t`: the new
  table is the table `w` times `t` divided by the sum of `t` over them. -/
  | chooses (w : ℕ) (over : List (ℕ × ℕ)) (t : Term K)
  /-- The new table is the table `w` times `t`. -/
  | weighs (w : ℕ) (t : Term K)
  /-- A choice is observed: the new table is the table `w` divided by its sum over the choices in
  `over`, the ones that remain uncertain. -/
  | observes (w : ℕ) (over : List (ℕ × ℕ))
  /-- The choices in `over` are forgotten: the new table is the sum of the table `w` over them. -/
  | forgets (w : ℕ) (over : List (ℕ × ℕ))

end

/-- A **program** has a list of steps, a term for the array to return, and the axes of that
array: choices with their sizes. -/
structure Program (K : Type u) : Type u where
  /-- The steps, in order. -/
  steps : List (Step K)
  /-- The term for the array that the program returns. -/
  ret : Term K
  /-- The choices that are the axes of the array, each with its size. -/
  axes : List (ℕ × ℕ)

variable {K : Type u} [Semifield K] [LinearOrder K]

mutual

/-- The **table of a term**, when `W` holds the tables so far. -/
def Term.eval (W : Array (Table K)) : Term K → Table K
  | .lit r => .const r
  | .op f ts =>
    let tables := Array.ofFn fun i ↦ (ts i).eval W
    .op f fun i ↦ tables.getD i (.const 0)
  | .val i size v => .ofFn [(i, size)] fun σ ↦ v (σ i)
  | .expect w over t => (t.eval W * W.getD w (.const 1)).sumOver over
  | .rename links t => (t.eval W).rename links
  | .best i size t => (t.eval W).best i size
  | .after s t => t.eval (W.push (s.table W))

/-- The **table of a step**: the table that it adds, when `W` holds the tables so far. -/
def Step.table (W : Array (Table K)) : Step K → Table K
  | .chooses w over t =>
    let x := t.eval W
    W.getD w (.const 1) * (x / x.sumOver over)
  | .weighs w t => W.getD w (.const 1) * t.eval W
  | .observes w over =>
    let x := W.getD w (.const 1)
    x / x.sumOver over
  | .forgets w over => (W.getD w (.const 1)).sumOver over

end

/-- The tables after a step: the tables so far and the new one. -/
def Step.run (W : Array (Table K)) (s : Step K) : Array (Table K) := W.push (s.table W)

/-- The table that a program returns: the table of its term after its steps. -/
def Program.table (p : Program K) : Table K := p.ret.eval (p.steps.foldl Step.run #[.const 1])

/-- The entries of the array of a program, in row-major order. -/
def Program.entries (p : Program K) : List K :=
  let t := p.table
  (Table.ofFn p.axes fun σ ↦ t.get σ).data.toList

/-- The rows of the array of a program: one list along the last axis for each choice of a position
on the other axes, in row-major order. -/
def Program.rows (p : Program K) : List (List K) :=
  let t := p.table
  match p.axes.getLast? with
  | none => [[t.get fun _ ↦ 0]]
  | some last =>
    (Table.positions (p.axes.dropLast.map (·.2))).map fun js ↦
      (List.range last.2).map fun j ↦ t.get (Table.assign p.axes (js ++ [j]))

end Memo
