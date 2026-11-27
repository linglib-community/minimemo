/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Interp
public import Minimemo.Table

/-!
# Terms

This file defines the arithmetic that a memo model asks for, with the names of the model removed,
and its value in a field of numbers.

Every choice of the model has a number and a domain. The tables that the model computes are
numbered in order. The table `0` has the number one, and each step of the model adds a table,
computed from the earlier ones. The belief of an agent at some moment, the probability of the
choices that the agent is uncertain of given the others, is one of these tables. A term denotes a
table. A program is a list of terms, one for each table that it adds, and a term for the array to
return.

A term is a literal, an operator applied to terms, the value of a choice, an earlier table, a sum
over choices, a term read at other choices, the places where a term is greatest, or a term after
another table is added. The statements of memo are written with these: a choice multiplies a
belief by a weight divided by its sum, an observation divides a belief by its sum, and an
expectation is a sum of a product.

A program has no numbers but rational literals. An interpretation gives the values of each
domain, the meaning of each operator, and the number of each literal, in some type of numbers;
`Memo.Interp.ofField` is the interpretation in an ordered field, in which the operators of memo
have their usual meaning.

For example, the model in which a speaker chooses one of three referents with equal weight, and
which returns the probability of each, adds the table `Term.chooses 0 [1] (.lit 1)`, a third along the
choice `1`, and returns `Term.expect 1 [1] (.op (.inl .eq) ![.val 1 R, .val 0 R])`.

## Main definitions

* `Memo.Term D F`: the terms.
* `Memo.Term.chooses`, `Memo.Term.weighs`, `Memo.Term.observes`, `Memo.Term.forgets`,
  `Memo.Term.expect`: the tables that the statements of memo add, as terms.
* `Memo.Program D F`: the domains of the choices, the terms of the tables, a term and the axes of
  the array.
* `Memo.Term.eval I size W t`: the table of the term `t`, when `W` holds the tables so far.
* `Memo.Program.entries I p`: the entries of the array of the program `p`, in row-major order.
* `Memo.Program.rows I p`: the same entries, as rows along the last axis.
-/

@[expose] public section

universe u

namespace Memo

/-- A **term** denotes a table of numbers that depends on choices. -/
inductive Term (D : Type u) (F : ℕ → Type u) : Type u
  /-- The rational literal `q`. -/
  | lit (q : ℚ)
  /-- The operator `o` applied to the terms `ts`. -/
  | op {k : ℕ} (o : Prim k ⊕ F k) (ts : Fin k → Term D F)
  /-- The value of the choice `i`, which is made from the domain `d`. -/
  | val (i : ℕ) (d : D)
  /-- The table with the number `w`. -/
  | ref (w : ℕ)
  /-- The sum of `t` over the choices in `over`. -/
  | sum (over : List ℕ) (t : Term D F)
  /-- The term `t` read at other choices: each choice `i` with a pair `(i, j)` in `links` is
  replaced by `j`. -/
  | rename (links : List (ℕ × ℕ)) (t : Term D F)
  /-- The number one where `t` is greatest along the choice `i`, and zero elsewhere. -/
  | best (i : ℕ) (t : Term D F)
  /-- The term `t₂` after the table of `t₁` is added. -/
  | letE (t₁ t₂ : Term D F)

namespace Term

variable {D : Type u} {F : ℕ → Type u}

/-- The product of two terms. -/
def mul (a b : Term D F) : Term D F := .op (.inl .mul) ![a, b]

/-- The quotient of two terms. -/
def div (a b : Term D F) : Term D F := .op (.inl .div) ![a, b]

/-- The belief `w` after the choices in `over` are made together with weight `t`: the table `w`
times `t` divided by the sum of `t` over them. -/
def chooses (w : ℕ) (over : List ℕ) (t : Term D F) : Term D F :=
  mul (.ref w) (div t (.sum over t))

/-- The belief `w` with its numbers multiplied by `t`. -/
def weighs (w : ℕ) (t : Term D F) : Term D F := mul (.ref w) t

/-- The belief `w` after a choice is observed: the table `w` divided by its sum over the choices
in `over`, the ones that remain uncertain. -/
def observes (w : ℕ) (over : List ℕ) : Term D F := div (.ref w) (.sum over (.ref w))

/-- The belief `w` after the choices in `over` are forgotten: the sum of the table `w` over
them. -/
def forgets (w : ℕ) (over : List ℕ) : Term D F := .sum over (.ref w)

/-- The expectation of `t` in the belief `w`: the sum of `t` times the table `w` over the choices
in `over`. -/
def expect (w : ℕ) (over : List ℕ) (t : Term D F) : Term D F := .sum over (mul t (.ref w))

end Term

/-- A **program** has the domains of its choices, in the order of their numbers, the terms of the
tables that it adds, a term for the array to return, and the choices that are the axes of that
array. -/
structure Program (D : Type u) (F : ℕ → Type u) : Type u where
  /-- The domain of each choice, in the order of the numbers of the choices. -/
  doms : List D
  /-- The terms of the tables that the program adds, in order. -/
  steps : List (Term D F)
  /-- The term for the array that the program returns. -/
  ret : Term D F
  /-- The choices that are the axes of the array. -/
  axes : List ℕ

/-- The term of a program: the term that it returns, after its tables are added in order. -/
def Program.term {D : Type u} {F : ℕ → Type u} (p : Program D F) : Term D F :=
  p.steps.foldr .letE p.ret

variable {D : Type u} {F : ℕ → Type u} {K : Type u} (I : Interp D F K)

/-- The size of the choice `i` of a program: the size of its domain. A number that is not the
number of a choice has the size one, so that every number has a position. -/
def Program.size (p : Program D F) (i : ℕ) : ℕ := (p.doms[i]?.map fun d ↦ (I.dom d).size).getD 1

variable [Semifield K] [LinearOrder K] (size : ℕ → ℕ)

/-- The **table of a term**, when `W` holds the tables so far. A link between two choices of
different sizes is not followed. -/
def Term.eval (W : Array (Table K)) : Term D F → Table K
  | .lit q => .const (I.lit q)
  | .op o ts =>
    let tables := Array.ofFn fun i ↦ (ts i).eval W
    .op size (I.op o) fun i ↦ tables.getD i (.const 0)
  | .val i d => .ofFn size [i] fun σ ↦ (I.dom d).val (σ i)
  | .ref w => W.getD w (.const 1)
  | .sum over t => (t.eval W).sumOver size over
  | .rename links t => (t.eval W).rename size (links.filter fun l ↦ size l.1 == size l.2)
  | .best i t => (t.eval W).best size i
  | .letE t₁ t₂ => t₂.eval (W.push (t₁.eval W))

/-- The table that a program returns: the table of its term, when the only table is the number
one. -/
def Program.table (p : Program D F) : Table K := p.term.eval I (p.size I) #[.const 1]

/-- The entries of the array of a program, in row-major order. -/
def Program.entries (p : Program D F) : List K :=
  let t := p.table I
  (Table.ofFn (p.size I) p.axes fun σ ↦ t.get (p.size I) σ).data.toList

/-- The rows of the array of a program: one list along the last axis for each choice of a position
on the other axes, in row-major order. -/
def Program.rows (p : Program D F) : List (List K) :=
  let t := p.table I
  match p.axes.getLast? with
  | none => [[t.get (p.size I) fun _ ↦ 0]]
  | some last =>
    (Table.positions (p.axes.dropLast.map (p.size I))).map fun js ↦
      (List.range (p.size I last)).map fun j ↦ t.get (p.size I) (Table.assign p.axes (js ++ [j]))

end Memo
