/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Syntax
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Interpretations

This file defines what the names of a model mean in a type of numbers.

A model has no numbers but rational literals. An interpretation gives the values of each domain,
the meaning of each operator, and the number of each literal. `Memo.Interp.ofField` is the
interpretation in an ordered field, in which the operators of memo have their usual meaning.

## Main definitions

* `Memo.Domain K`: a finite sequence of numbers, the values that a choice can take.
* `Memo.Interp D F K`: an interpretation of domains, operators and literals in the numbers `K`.
* `Memo.Prim.eval`: the meaning of the operators of memo in an ordered field.
* `Memo.Interp.ofField dom call`: the interpretation in an ordered field.
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
def Domain.index {K : Type*} [BEq K] (X : Domain K) (v : K) : ℕ :=
  ((List.range X.size).find? fun j ↦ X.val j == v).getD 0

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

end Memo
