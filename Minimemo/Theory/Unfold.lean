/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Theory.Denote

/-!
# From a program to its equations

This file turns the meaning of a program into an equation for the meaning of each of its tables
in terms of those before it, so that a result about a model is proved from the model.

A program is a list of terms, one for each statement of the model, and a returned term. The
tactic `memo_unfold` names the meaning of each term in order, and rewrites it with the meaning of
the operators of memo: a choice multiplies the belief by the weight divided by its sum, an
observation divides the belief by its sum, an expectation is a sum. What is left is a goal about
the named meanings, with a hypothesis for each: the model as equations.

The meanings are named and not substituted, so that a table that several later tables use is
written once.

## Main definitions

* `memo_unfold [lemmas]`: unfolds the meaning of a program, with the definitions of the program,
  of its domains and of its outside functions as `lemmas`.

## Main results

* `Memo.denote_letE_eq_of`: the step that names the meaning of a table.
* `Memo.denote_app_prim`, `Memo.denote_app_fn`, `Memo.denote_sum`, `Memo.denote_rename`,
  `Memo.denote_ref`, `Memo.denote_val`, `Memo.denote_lit`: the meaning of each term, in an ordered
  field.
-/

@[expose] public section

namespace Memo

variable {D : Type} {F : ℕ → Type} {K : Type} [Field K] [LinearOrder K]
  (dom : D → Domain K) (call : {k : ℕ} → F k → (Fin k → K) → K) (size : ℕ → ℕ)
  (Φ : List ((ℕ → ℕ) → K))

theorem denote_lit (q : ℚ) (σ) :
    (Term.lit q : Term D F).denote (.ofField dom call) size Φ σ = (q : K) := rfl
theorem denote_val (i : ℕ) (d : D) (σ) :
    (Term.val i d : Term D F).denote (.ofField dom call) size Φ σ = (dom d).val (σ i) := rfl
theorem denote_ref (w : ℕ) :
    (Term.ref w : Term D F).denote (.ofField dom call) size Φ = Φ.getD w fun _ ↦ 1 := rfl
theorem denote_letE (a b : Term D F) :
    (Term.letE a b).denote (.ofField dom call) size Φ =
      b.denote (.ofField dom call) size (Φ ++ [a.denote (.ofField dom call) size Φ]) := rfl
theorem denote_sum (over : List ℕ) (t : Term D F) :
    (Term.sum over t).denote (.ofField dom call) size Φ =
      sumList size over (t.denote (.ofField dom call) size Φ) := rfl
theorem denote_rename (links : List (ℕ × ℕ)) (t : Term D F) (σ) :
    (Term.rename links t).denote (.ofField dom call) size Φ σ =
      t.denote (.ofField dom call) size Φ fun i ↦
        σ (((links.filter fun l ↦ size l.1 == size l.2).lookup i).getD i) := rfl
theorem denote_app_prim {k : ℕ} (p : Prim k) (ts : List (Term D F)) (σ) :
    (Term.app (.inl p) ts).denote (.ofField dom call) size Φ σ =
      p.eval fun i ↦ (ts.getD i (.lit 0)).denote (.ofField dom call) size Φ σ := rfl
theorem denote_app_fn {k : ℕ} (f : F k) (ts : List (Term D F)) (σ) :
    (Term.app (.inr f) ts).denote (.ofField dom call) size Φ σ =
      call f fun i ↦ (ts.getD i (.lit 0)).denote (.ofField dom call) size Φ σ := rfl
omit [LinearOrder K] in
theorem sumList_nil (f : (ℕ → ℕ) → K) : sumList size [] f = f := rfl
omit [LinearOrder K] in
theorem sumList_cons (i : ℕ) (is : List ℕ) (f : (ℕ → ℕ) → K) :
    sumList size (i :: is) f =
      sumList size is fun σ ↦ ∑ j ∈ Finset.range (size i), f (Function.update σ i j) := rfl

omit [LinearOrder K] in
theorem sumList_singleton (i : ℕ) (f : (ℕ → ℕ) → K) (σ) :
    sumList size [i] f σ = ∑ j ∈ Finset.range (size i), f (Function.update σ i j) := rfl

/-- To find the meaning of `letE a b`, name the meaning of `a`. -/
theorem denote_letE_eq_of (a b : Term D F) (σ : ℕ → ℕ) (X : K)
    (h : ∀ f : (ℕ → ℕ) → K, (∀ τ, f τ = a.denote (.ofField dom call) size Φ τ) →
      b.denote (.ofField dom call) size (Φ ++ [f]) σ = X) :
    (Term.letE a b).denote (.ofField dom call) size Φ σ = X :=
  h _ fun _ ↦ rfl

/-- Unfolds the meaning of a program into an equation for the meaning of each of its tables in
terms of those before it. -/
syntax "memo_unfold" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| memo_unfold $[[$ls,*]]?) => do
    let extra := (ls.map (·.getElems)).getD #[]
    `(tactic| (
      simp only [Program.term, List.foldr]
      repeat (refine denote_letE_eq_of _ _ _ _ _ _ _ _ fun f h ↦ ?_)
      simp only [Term.chooses, Term.weighs, Term.observes, Term.forgets, Term.expect, Term.mul,
        Term.div, denote_app_prim, denote_app_fn, denote_ref, denote_sum, denote_rename,
        denote_lit, denote_val, sumList_singleton, sumList_nil, Prim.eval, List.getD_cons_zero,
        List.getD_cons_succ, List.cons_append, List.nil_append, Fin.val_zero, Fin.val_one,
        Fin.isValue, List.filter_nil, List.lookup_nil, Option.getD_none, List.foldr_nil,
        List.foldr_cons, $extra,*] at *))

end Memo
