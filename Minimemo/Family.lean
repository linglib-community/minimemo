/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Model

/-!
# Models that refer to models

This file defines a family of models in which a model may refer to other members, as a model of
memo refers to itself with other parameters, and gives the array of each member.

In memo, `L[u, r](t - 1)` inside the model `L` with the parameter `t` is the entry at `u` and `r`
of the array of `L` with the parameter `t - 1`. Here the members of a family are indexed by their
parameters. A model of the family uses the outside functions of `Refs R F`: a reference, which is
a name in `R`, or an outside function in `F`. The family says which member a reference names, in
each member. So `L` above is a family indexed by `t`, with one reference, which in the member `t`
names the member `t - 1`.

A reference applied to expressions is the entry of the array of the member that it names, at the
values of the expressions.

## Main definitions

* `Memo.Refs R F`: the outside functions of a model that may refer to models.
* `Memo.Expr.ref r es`, `Memo.Expr.fn f es`: a reference and an outside function, applied.
* `Memo.Family A N D F P R`: a family of models indexed by `P`, with the references `R`.
* `Memo.Model.refs M`: the references in a model.
* `Memo.Family.call`: the meaning of references and outside functions in a member, when the
  arrays of the members are given.
* `Memo.Family.entries fam of dom fn n p`: the array of the member `p`, where references are
  followed to the depth `n`.

## Implementation notes

`Memo.Family.entries` is defined by recursion on a depth, so that Lean evaluates it. A reference
at the depth zero reads an empty array, whose entries are zero. So the array of a member is right
when the depth is at least the number of references that are followed from it, one inside the
other.
-/

@[expose] public section

universe u v

namespace Memo

/-- The outside functions of a model that may refer to models: a reference in `R`, with any number
of arguments, or an outside function in `F`. -/
abbrev Refs (R : Type u) (F : ℕ → Type u) : ℕ → Type u := fun k ↦ R ⊕ F k

variable {A N D R : Type u} {F : ℕ → Type u}

/-- The reference `r` applied to the expressions `es`: the entry, at their values, of the array of
the model that `r` names. -/
abbrev Expr.ref {k : ℕ} (r : R) (es : Fin k → Expr A N D (Refs R F)) : Expr A N D (Refs R F) :=
  .op (.inr (.inl r)) es

/-- The outside function `f` applied to the expressions `es`, in a model that may refer to
models. -/
abbrev Expr.fn {k : ℕ} (f : F k) (es : Fin k → Expr A N D (Refs R F)) : Expr A N D (Refs R F) :=
  .op (.inr (.inr f)) es

mutual

/-- The references in an expression. -/
def Expr.refs : Expr A N D (Refs R F) → List R
  | .lit _ | .choice _ | .entropy .. | .divergence .. => []
  | .op (.inr (.inl r)) es => r :: (List.finRange _).flatMap fun i ↦ Expr.refs (es i)
  | .op _ es => (List.finRange _).flatMap fun i ↦ Expr.refs (es i)
  | .query _ e | .expect e => Expr.refs e
  | .imagine s e => Stmt.refs s ++ Expr.refs e

/-- The references in a statement. -/
def Stmt.refs : Stmt A N D (Refs R F) → List R
  | .chooses _ _ _ e | .choosesMax _ _ _ e | .choosesMany _ _ e | .observesEvent _ e => Expr.refs e
  | .thinks _ s => Stmt.refs s
  | .seq s₁ s₂ => Stmt.refs s₁ ++ Stmt.refs s₂
  | .observes .. | .knows .. | .snapshot .. | .variant .. | .forgets .. | .pass => []

end

/-- The references in a model. -/
def Model.refs (M : Model A N D (Refs R F)) : List R := Stmt.refs M.body ++ Expr.refs M.ret

/-- A **family of models** indexed by `P`: a model for each index, which may use the references in
`R`, and the member that each reference names in each member. -/
structure Family (A N D : Type u) (F : ℕ → Type u) (P : Type v) (R : Type u) where
  /-- The member at each index. -/
  model : P → Model A N D (Refs R F)
  /-- The index of the member that a reference names, in the member at an index. -/
  target : P → R → P

variable {P : Type v} {K : Type u} [Zero K] [BEq K] (fam : Family A N D F P R)
  (of : (D → Domain K) → ({k : ℕ} → Refs R F k → (Fin k → K) → K) → Interp D (Refs R F) K)
  (dom : D → Domain K) (fn : {k : ℕ} → F k → (Fin k → K) → K)

/-- The meaning of the references and the outside functions in the member `p` of a family, when
`below q` is the array of the member `q`. -/
def Family.call (below : P → List K) (p : P) : {k : ℕ} → Refs R F k → (Fin k → K) → K
  | _, .inr f => fn f
  | k, .inl r =>
    let q := fam.target p r
    let doms := (fam.model q).axes.map fun a ↦ dom a.2
    let entries := below q
    fun v ↦ Model.lookup doms entries fun i ↦ if h : i < k then v ⟨i, h⟩ else 0

variable [One K] [Add K] [LE K] [DecidableLE K] [DecidableEq A] [DecidableEq N] [DecidableEq D]
  [BEq P]

/-- The **array of a member** of a family, with the entries in row-major order, where references
are followed to the depth `n`. The interpretation is `of`, which is `Interp.ofField` in an ordered
field, with the domains `dom` and the outside functions `fn`. The arrays of the members that the
member refers to are computed first, each once. -/
def Family.entries : ℕ → P → List K
  | 0, _ => []
  | n + 1, p =>
    let arrays := (fam.model p).refs.map fun r ↦
      (fam.target p r, Family.entries n (fam.target p r))
    (Model.entries (of dom (fam.call dom fn (fun q ↦ (arrays.lookup q).getD []) p))
      (fam.model p)).getD []

end Memo
