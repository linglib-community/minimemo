/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Syntax.Basic
public import Minimemo.Table.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Programs on tables

This file defines the arithmetic that a memo model asks for, with the names of the model removed,
and its value in a field of numbers.

Every choice of the model has a number and a domain. The tables that the model computes are
numbered in order. The table `0` has the number one, and each step adds a table, computed from the
earlier ones. The belief of an agent at some moment, the probability of the choices that the
agent is uncertain of given the others, is one of these tables. A term denotes a table. A program
is a list of steps and a term for the array to return.

A program has no numbers but rational literals. An interpretation gives the values of each
domain, the meaning of each operator, and the number of each literal, in some type of numbers;
`Memo.Interp.ofField` is the interpretation in an ordered field, in which the operators of memo
have their usual meaning.

For example, the model in which a speaker chooses one of three referents with equal weight, and
which returns the probability of each, is the step `.chooses 0 [1] (.lit 1)`, which adds the table
`1`, a third along the choice `1`, and the term
`.expect 1 [1] (.op (.inl .eq) ![.val 1 R, .val 0 R])`.

## Main definitions

* `Memo.Domain K`: a finite sequence of numbers, the values that a choice can take.
* `Memo.Interp D F K`: an interpretation of domains, operators and literals in the numbers `K`.
* `Memo.Term D F`: a literal, an operator applied to terms, the value of a choice, an expectation,
  a term read at other choices, or a term after a step.
* `Memo.Step D F`: a choice, a weight, an observation or a forgetting.
* `Memo.Program D F`: the domains of the choices, a list of steps, a term and the axes of the
  array.
* `Memo.Term.eval I size W t`: the table of the term `t`, when `W` holds the tables so far.
* `Memo.Step.table I size W s`: the table that the step `s` adds.
* `Memo.Program.entries I p`: the entries of the array of the program `p`, in row-major order.
* `Memo.Program.rows I p`: the same entries, as rows along the last axis.
-/

@[expose] public section

universe u

namespace Memo

/-- A **domain** is a finite sequence of numbers, the values that a choice can take. -/
structure Domain (K : Type*) where
  /-- The number of values. -/
  size : ℕ
  /-- The value at each position. -/
  val : ℕ → K

/-- The first position at which a domain has the value `v`, or zero if it has none. -/
def Domain.index {K : Type*} [DecidableEq K] (X : Domain K) (v : K) : ℕ :=
  ((List.range X.size).find? fun j ↦ X.val j = v).getD 0

/-- An **interpretation** gives the values of each domain, the meaning of each operator, and the
number of each rational literal. -/
structure Interp (D : Type u) (F : ℕ → Type u) (K : Type u) where
  /-- The values of each domain. -/
  dom : D → Domain K
  /-- The meaning of each operator. -/
  op : {k : ℕ} → Prim k ⊕ F k → (Fin k → K) → K
  /-- The number of each rational literal. -/
  lit : ℚ → K

/-- The meaning of the operators of memo in an ordered field. -/
def Prim.eval {K : Type*} [Field K] [LinearOrder K] : {k : ℕ} → Prim k → (Fin k → K) → K
  | _, .add, v => v 0 + v 1
  | _, .sub, v => v 0 - v 1
  | _, .mul, v => v 0 * v 1
  | _, .div, v => v 0 / v 1
  | _, .eq, v => if v 0 = v 1 then 1 else 0
  | _, .ne, v => if v 0 = v 1 then 0 else 1
  | _, .lt, v => if v 0 < v 1 then 1 else 0
  | _, .le, v => if v 0 ≤ v 1 then 1 else 0
  | _, .both, v => if v 0 ≠ 0 ∧ v 1 ≠ 0 then 1 else 0
  | _, .either, v => if v 0 ≠ 0 ∨ v 1 ≠ 0 then 1 else 0
  | _, .neg, v => -v 0
  | _, .abs, v => |v 0|
  | _, .truthy, v => if v 0 ≠ 0 then 1 else 0
  | _, .pow n, v => v 0 ^ n
  | _, .ite, v => if v 0 ≠ 0 then v 1 else v 2

/-- The **interpretation in an ordered field**: the operators of memo have their usual meaning, a
literal is its cast, and the domains and the outside functions are given. -/
def Interp.ofField {D : Type u} {F : ℕ → Type u} {K : Type u} [Field K] [LinearOrder K]
    (dom : D → Domain K) (call : {k : ℕ} → F k → (Fin k → K) → K) : Interp D F K where
  dom := dom
  op o := match o with
    | .inl p => p.eval
    | .inr f => call f
  lit q := q

mutual

/-- A **term** denotes a table of numbers that depends on choices. -/
inductive Term (D : Type u) (F : ℕ → Type u) : Type u
  /-- The rational literal `q`. -/
  | lit (q : ℚ)
  /-- The operator `o` applied to the terms `ts`. -/
  | op {k : ℕ} (o : Prim k ⊕ F k) (ts : Fin k → Term D F)
  /-- The value of the choice `i`, which is made from the domain `d`. -/
  | val (i : ℕ) (d : D)
  /-- The expectation of `t` in the belief `w`: the sum of `t` times the table `w` over the
  choices in `over`. -/
  | expect (w : ℕ) (over : List ℕ) (t : Term D F)
  /-- The term `t` read at other choices: each choice `i` with a pair `(i, j)` in `links` is
  replaced by `j`. -/
  | rename (links : List (ℕ × ℕ)) (t : Term D F)
  /-- The number one where `t` is greatest along the choice `i`, and zero elsewhere. -/
  | best (i : ℕ) (t : Term D F)
  /-- The term `t` if the step `s` were to happen. -/
  | after (s : Step D F) (t : Term D F)

/-- A **step** adds a table, computed from the tables so far. -/
inductive Step (D : Type u) (F : ℕ → Type u) : Type u
  /-- The choices in `over` are made together with weight `t`: the new table is the table `w`
  times `t` divided by the sum of `t` over them. -/
  | chooses (w : ℕ) (over : List ℕ) (t : Term D F)
  /-- The new table is the table `w` times `t`. -/
  | weighs (w : ℕ) (t : Term D F)
  /-- A choice is observed: the new table is the table `w` divided by its sum over the choices in
  `over`, the ones that remain uncertain. -/
  | observes (w : ℕ) (over : List ℕ)
  /-- The choices in `over` are forgotten: the new table is the sum of the table `w` over them. -/
  | forgets (w : ℕ) (over : List ℕ)

end

/-- A **program** has the domains of its choices, in the order of their numbers, a list of steps,
a term for the array to return, and the choices that are the axes of that array. -/
structure Program (D : Type u) (F : ℕ → Type u) : Type u where
  /-- The domain of each choice, in the order of the numbers of the choices. -/
  doms : List D
  /-- The steps, in order. -/
  steps : List (Step D F)
  /-- The term for the array that the program returns. -/
  ret : Term D F
  /-- The choices that are the axes of the array. -/
  axes : List ℕ

/-- A list of choices, each with its size. -/
def withSizes (size : ℕ → ℕ) (I : List ℕ) : List (ℕ × ℕ) := I.map fun i ↦ (i, size i)

variable {D : Type u} {F : ℕ → Type u} {K : Type u} (I : Interp D F K)

/-- The size of the choice `i` of a program: the size of its domain. -/
def Program.size (p : Program D F) (i : ℕ) : ℕ := (p.doms[i]?.map fun d ↦ (I.dom d).size).getD 0

variable [Semifield K] [LinearOrder K] (size : ℕ → ℕ)

mutual

/-- The **table of a term**, when `W` holds the tables so far. A link between two choices of
different sizes is not followed. -/
def Term.eval (W : Array (Table K)) : Term D F → Table K
  | .lit q => .const (I.lit q)
  | .op o ts =>
    let tables := Array.ofFn fun i ↦ (ts i).eval W
    .op (I.op o) fun i ↦ tables.getD i (.const 0)
  | .val i d => .ofFn [(i, size i)] fun σ ↦ (I.dom d).val (σ i)
  | .expect w over t => (t.eval W * W.getD w (.const 1)).sumOver (withSizes size over)
  | .rename links t => (t.eval W).rename (links.filter fun l ↦ size l.1 == size l.2)
  | .best i t => (t.eval W).best i (size i)
  | .after s t => t.eval (W.push (s.table W))

/-- The **table of a step**: the table that it adds, when `W` holds the tables so far. -/
def Step.table (W : Array (Table K)) : Step D F → Table K
  | .chooses w over t =>
    let x := t.eval W
    W.getD w (.const 1) * (x / x.sumOver (withSizes size over))
  | .weighs w t => W.getD w (.const 1) * t.eval W
  | .observes w over =>
    let x := W.getD w (.const 1)
    x / x.sumOver (withSizes size over)
  | .forgets w over => (W.getD w (.const 1)).sumOver (withSizes size over)

end

/-- The tables after a step: the tables so far and the new one. -/
def Step.run (W : Array (Table K)) (s : Step D F) : Array (Table K) := W.push (s.table I size W)

/-- The table that a program returns: the table of its term after its steps. -/
def Program.table (p : Program D F) : Table K :=
  p.ret.eval I (p.size I) (p.steps.foldl (Step.run I (p.size I)) #[.const 1])

/-- The entries of the array of a program, in row-major order. -/
def Program.entries (p : Program D F) : List K :=
  let t := p.table I
  (Table.ofFn (withSizes (p.size I) p.axes) fun σ ↦ t.get σ).data.toList

/-- The rows of the array of a program: one list along the last axis for each choice of a position
on the other axes, in row-major order. -/
def Program.rows (p : Program D F) : List (List K) :=
  let t := p.table I
  let axes := withSizes (p.size I) p.axes
  match axes.getLast? with
  | none => [[t.get fun _ ↦ 0]]
  | some last =>
    (Table.positions (axes.dropLast.map (·.2))).map fun js ↦
      (List.range last.2).map fun j ↦ t.get (Table.assign axes (js ++ [j]))

end Memo
