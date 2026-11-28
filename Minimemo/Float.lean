/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Model

/-!
# Running a model in floating point

This file gives the interpretation of a model in floating-point numbers, in which a model that
uses the exponential or the logarithm can be run.

The rational numbers have no exponential, so such a model has no array of rational numbers. Its
meaning is in the real numbers, where nothing is computed. Floating point is for running the
model: `#eval Model.entries (.ofFloat dom call) m` prints its array, as memo does.

## Main definitions

* `Memo.Prim.float`: the operators of memo in floating point.
* `Memo.Exp.float`: the exponential, the logarithm and the power in floating point.
* `Memo.Interp.ofFloat dom call`: the interpretation in floating point.
-/

@[expose] public section

namespace Memo

/-- The operators of memo in floating point. -/
def Prim.float : {k : ℕ} → Prim k → (Fin k → Float) → Float
  | _, .add, v => v 0 + v 1
  | _, .sub, v => v 0 - v 1
  | _, .mul, v => v 0 * v 1
  | _, .div, v => v 0 / v 1
  | _, .eq, v => if v 0 == v 1 then 1 else 0
  | _, .ne, v => if v 0 == v 1 then 0 else 1
  | _, .lt, v => if v 0 < v 1 then 1 else 0
  | _, .le, v => if v 0 ≤ v 1 then 1 else 0
  | _, .both, v => if v 0 != 0 && v 1 != 0 then 1 else 0
  | _, .either, v => if v 0 != 0 || v 1 != 0 then 1 else 0
  | _, .neg, v => -v 0
  | _, .abs, v => (v 0).abs
  | _, .truthy, v => if v 0 != 0 then 1 else 0
  | _, .pow n, v => (v 0).pow n.toFloat
  | _, .ite, v => if v 0 != 0 then v 1 else v 2

/-- The exponential, the logarithm and the power in floating point. -/
def Exp.float : {k : ℕ} → Exp k → (Fin k → Float) → Float
  | _, .exp, v => (v 0).exp
  | _, .log, v => (v 0).log
  | _, .rpow, v => (v 0).pow (v 1)
  | _, .mod, v => v 0 - v 1 * (v 0 / v 1).floor
  | _, .negMulLog, v => if v 0 == 0 then 0 else -(v 0 * (v 0).log)
  | _, .klTerm, v =>
    -- memo keeps the difference of the logarithms finite, within single precision
    let d := (v 0).log - (v 1).log
    let big : Float := 3.4028234663852886e38
    v 0 * (if d.isNaN then 0 else if d > big then big else if d < -big then -big else d)

/-- The **interpretation in floating point**: the operators of memo are those of floating point,
a literal is its quotient, and the domains and the outside functions are given. -/
def Interp.ofFloat {D : Type} {F : ℕ → Type} (dom : D → Domain Float)
    (call : {k : ℕ} → F k → (Fin k → Float) → Float) : Interp D F Float where
  dom := dom
  op o := match o with
    | .inl p => p.float
    | .inr f => call f
  lit q := Float.ofInt q.num / q.den.toFloat

end Memo
