/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Syntax
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Interpretations

This file defines what the names of a model mean in a type of numbers.

A model has no numbers but rational literals. An interpretation gives the values of each domain,
the meaning of each operator, and the number of each literal. `Memo.Interp.ofField` is the
interpretation in an ordered field, in which the operators of memo have their usual meaning.

Two interpretations are compatible along a map `φ` of numbers if their domains have the same
sizes, and the values, the operators and the literals of the second are the images of those of the
first. The interpretations in two ordered fields are compatible along an embedding that preserves
the order.

## Main definitions

* `Memo.Domain K`: a finite sequence of numbers, the values that a choice can take.
* `Memo.Interp D F K`: an interpretation of domains, operators and literals in the numbers `K`.
* `Memo.Prim.eval`: the meaning of the operators of memo in an ordered field.
* `Memo.Interp.ofField dom call`: the interpretation in an ordered field.
* `Memo.Interp.Arith I`: the interpretation `I` gives the product and the quotient their meaning.
* `Memo.Interp.Compat φ I J`: the interpretations `I` and `J` are compatible along `φ`.

## Main results

* `Memo.Interp.compat_ofField`: the interpretations in two ordered fields are compatible.
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

variable {D : Type u} {F : ℕ → Type u} {K L : Type u}

/-- An interpretation gives the product and the quotient their meaning. -/
structure Interp.Arith [Semifield K] (J : Interp D F K) : Prop where
  mul : ∀ x : Fin 2 → K, J.op (.inl .mul) x = x 0 * x 1
  div : ∀ x : Fin 2 → K, J.op (.inl .div) x = x 0 / x 1

/-- Two interpretations are **compatible** along `φ` if their domains have the same sizes, and the
values, the operators and the literals of the second are the images of those of the first. -/
structure Interp.Compat (φ : K → L) (I : Interp D F K) (J : Interp D F L) : Prop where
  size : ∀ d, (J.dom d).size = (I.dom d).size
  val : ∀ d j, (J.dom d).val j = φ ((I.dom d).val j)
  op : ∀ {k : ℕ} (o : Prim k ⊕ F k) (x : Fin k → K), J.op o (fun i ↦ φ (x i)) = φ (I.op o x)
  lit : ∀ q, J.lit q = φ (I.lit q)

/-- The interpretations in two ordered fields are compatible along an embedding that preserves the
order, if the domains and the outside functions are. -/
theorem Interp.compat_ofField [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Field L]
    [LinearOrder L] [IsStrictOrderedRing L] {φ : K →+* L} (hφ : StrictMono φ)
    {dom : D → Domain K} {dom' : D → Domain L} {call : {k : ℕ} → F k → (Fin k → K) → K}
    {call' : {k : ℕ} → F k → (Fin k → L) → L} (hsize : ∀ d, (dom' d).size = (dom d).size)
    (hval : ∀ d j, (dom' d).val j = φ ((dom d).val j))
    (hcall : ∀ {k : ℕ} (f : F k) (x : Fin k → K), call' f (fun i ↦ φ (x i)) = φ (call f x)) :
    Interp.Compat φ (.ofField dom call) (.ofField dom' call') where
  size := hsize
  val := hval
  lit q := (map_ratCast φ q).symm
  op o x := by
    rcases o with p | f
    · cases p <;>
        simp [Interp.ofField, Prim.eval, hφ.injective.eq_iff, hφ.lt_iff_lt, hφ.le_iff_le,
          apply_ite φ, abs_eq_max_neg, hφ.monotone.map_max]
    · exact hcall f x

end Memo
