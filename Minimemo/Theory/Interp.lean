/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Interp
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Compatible interpretations

This file relates two interpretations of the names of a model.

Two interpretations are compatible along a map `φ` of numbers if their domains have the same
sizes, and the values, the operators and the literals of the second are the images of those of the
first. The interpretations in two ordered fields are compatible along an embedding that preserves
the order.

## Main definitions

* `Memo.Interp.Arith I`: the interpretation `I` gives the product and the quotient their meaning.
* `Memo.Interp.Compat φ I J`: the interpretations `I` and `J` are compatible along `φ`.

## Main results

* `Memo.Interp.compat_ofField`: the interpretations in two ordered fields are compatible.
-/

@[expose] public section

universe u

namespace Memo

variable {D : Type u} {F : ℕ → Type u} {K L : Type u}

/-- An interpretation gives the product and the quotient their meaning. -/
structure Interp.Arith [Semifield K] (J : Interp D F K) : Prop where
  mul : ∀ x : Fin 2 → K, J.op (.inl .mul) x = x 0 * x 1
  div : ∀ x : Fin 2 → K, J.op (.inl .div) x = x 0 / x 1

/-- The interpretation in an ordered field gives the product and the quotient their meaning. -/
theorem Interp.arith_ofField [Field K] [LinearOrder K] (dom : D → Domain K)
    (call : {k : ℕ} → F k → (Fin k → K) → K) : (Interp.ofField dom call).Arith :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

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
