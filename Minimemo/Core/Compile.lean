/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Core.Program
public import Minimemo.Syntax
public import Minimemo.Tensor

/-!
# From a model to a program

This file translates a memo model to a program on tables.

The translation reads the statements in order and keeps, for every agent's model of the world, a
scope: the choices that the agent is aware of, each with its number and whether the agent is
certain of it, and the scopes of the agents that this agent has a model of. It computes no number.
It checks that every expression is used where the agent can compute it, and it writes the steps
of the program.

A choice that an agent imagines has its own number. When the agent observes it, the agent becomes
certain of that choice, and the scope records a link from it to the choice that was observed. A
term that leaves the agent's mind, in a query or as the weight of the agent's choice, is read
through these links.

## Main definitions

* `Memo.Core.Scope A N D`: the choices and agents that a mind is aware of.
* `Memo.Core.Expr.term dom e S`: the term of the expression `e` in the scope `S`, with the choices
  that it depends on.
* `Memo.Core.Stmt.steps dom s S g`: the scope after the statement `s`, with its steps added to
  `g`.
* `Memo.Core.Model.program dom M`: the program of the model `M`.
* `Memo.Core.Model.entries dom M`: the entries of the array of `M`, in row-major order.
* `Memo.Core.Model.covered M`: the model uses only the statements and expressions that the
  translation has.

## Implementation notes

The translation has every statement but `snapshots_self_as` and `forgets_about`, and every
expression but `imagine`. On a model with one of these the program is `none`, as it is for a model that memo does not accept; `Memo.Core.Model.covered` tells the two
apart.
-/

@[expose] public section

universe u

namespace Memo.Core

/-- A choice in a scope has a number, a domain, and a flag that says whether the agent of the
scope is certain of its value. -/
structure Entry (D : Type u) : Type u where
  /-- The number of the choice. -/
  index : ℕ
  /-- The domain that the value is chosen from. -/
  dom : D
  /-- Whether the agent is certain of the value. -/
  certain : Bool

/-- A **scope** is what a mind is aware of: its number, its choices by the agent who makes them
and their name, the scopes of the agents that it has a model of, and a link from each choice that
it has observed to the choice that it equals outside. -/
structure Scope (A N D : Type u) : Type u where
  /-- The number of the mind. -/
  mind : ℕ
  /-- The choices that the mind is aware of. -/
  entries : List ((Ref A × N) × Entry D)
  /-- The scopes of the agents that the mind has a model of. -/
  agents : A → Option (Scope A N D)
  /-- The observed choices, each with the choice outside that it equals. -/
  links : List (ℕ × ℕ)

/-- The next free number of a choice, the next free number of a mind, and the steps so far. -/
structure Gen (K : Type u) : Type u where
  /-- The next free number of a choice. -/
  next : ℕ
  /-- The next free number of a mind. -/
  minds : ℕ
  /-- The steps so far. -/
  steps : Array (Step K)

variable {A N D K : Type u} [DecidableEq A] [DecidableEq N] [DecidableEq D]

namespace Scope

/-- The choices that the mind is certain of. -/
def certain (S : Scope A N D) : List ℕ :=
  S.entries.filterMap fun e ↦ if e.2.certain then some e.2.index else none

/-- The choices that the mind is uncertain of, each with its size. -/
def uncertain (dom : D → Domain K) (S : Scope A N D) : List (ℕ × ℕ) :=
  (S.entries.filterMap fun e ↦
    if e.2.certain then none else some (e.2.index, (dom e.2.dom).size)).dedup

/-- The scope with the choice at `a` set to `e`. -/
def insert (S : Scope A N D) (a : Ref A × N) (e : Entry D) : Scope A N D :=
  { S with entries := (a, e) :: S.entries.filter fun p ↦ p.1 ≠ a }

/-- The scope of the agent `α` in a scope, or a new empty one with the next free number. -/
def agent (S : Scope A N D) (α : A) (g : Gen K) : Scope A N D × Gen K :=
  match S.agents α with
  | some Sα => (Sα, g)
  | none => (⟨g.minds, [], fun _ ↦ none, []⟩, { g with minds := g.minds + 1 })

/-- The choice that a choice of the scope equals outside. -/
def link (S : Scope A N D) (i : ℕ) : ℕ := (S.links.lookup i).getD i

end Scope

/-- The values of a family of options, if every one of them is defined. -/
def allSome {k : ℕ} {β : Type*} (o : Fin k → Option β) : Option (Fin k → β) :=
  if h : ∀ i, (o i).isSome then some fun i ↦ (o i).get (h i) else none

variable (dom : D → Domain K)

/-- The **term of an expression** in a scope, with the choices that it depends on. -/
def Expr.term (e : Expr A N D K) (S : Scope A N D) : Option (Term K × List ℕ) :=
  match e with
  | .lit r => some (.lit r, [])
  | .op f es =>
    (allSome fun i ↦ Expr.term (es i) S).map fun ts ↦
      (.op f fun i ↦ (ts i).1, ((List.finRange _).flatMap fun i ↦ (ts i).2).dedup)
  | .choice x =>
    (S.entries.lookup (.self, x)).map fun c ↦
      (.val c.index (dom c.dom).size (dom c.dom).val, [c.index])
  | .query α e => do
    let Sα ← S.agents α
    let (t, deps) ← Expr.term e Sα
    if deps.all (· ∈ Sα.certain) then some (.rename Sα.links t, (deps.map Sα.link).dedup)
    else none
  | .expect e => do
    let (t, deps) ← Expr.term e S
    if deps.all (· ∈ S.certain) then some (t, deps)
    else some (.expect S.mind (S.uncertain dom) t, S.certain)
  | .imagine _ _ => none

/-- The scope after a **statement**, with the steps of the statement added. -/
def Stmt.steps (s : Stmt A N D K) (S : Scope A N D) (g : Gen K) : Option (Scope A N D × Gen K) :=
  match s with
  | .pass => some (S, g)
  | .seq s₁ s₂ => do
    let (S', g') ← Stmt.steps s₁ S g
    Stmt.steps s₂ S' g'
  | .thinks α s => do
    let (Sα, g) := S.agent α g
    let (Sα', g') ← Stmt.steps s Sα g
    some ({ S with agents := Function.update S.agents α (some Sα') }, g')
  | .chooses α x X e => do
    let (Sα, g) := S.agent α g
    let Sα' := Sα.insert (.self, x) ⟨g.next, X, true⟩
    let (t, deps) ← Expr.term dom e Sα'
    if deps.all (· ∈ Sα'.certain) ∧ (Sα.entries.lookup (.self, x)).isNone then
      some ({ S.insert (.agent α, x) ⟨g.next, X, false⟩ with
          agents := Function.update S.agents α (some Sα') },
        { g with
          next := g.next + 1
          steps := g.steps.push (.chooses S.mind [(g.next, (dom X).size)] (.rename Sα'.links t)) })
    else none
  | .choosesMax α x X e => do
    let (Sα, g) := S.agent α g
    let Sα' := Sα.insert (.self, x) ⟨g.next, X, true⟩
    let (t, deps) ← Expr.term dom e Sα'
    if deps.all (· ∈ Sα'.certain) ∧ (Sα.entries.lookup (.self, x)).isNone then
      some ({ S.insert (.agent α, x) ⟨g.next, X, false⟩ with
          agents := Function.update S.agents α (some Sα') },
        { g with
          next := g.next + 1
          steps := g.steps.push (.chooses S.mind [(g.next, (dom X).size)]
            (.rename Sα'.links (.best g.next (dom X).size t))) })
    else none
  | .choosesMany α xs e => do
    let (Sα, g) := S.agent α g
    let Sα' := xs.zipIdx.foldl (fun S p ↦ S.insert (.self, p.1.1) ⟨g.next + p.2, p.1.2, true⟩) Sα
    let (t, deps) ← Expr.term dom e Sα'
    if deps.all (· ∈ Sα'.certain) ∧ xs.all fun p ↦ (Sα.entries.lookup (.self, p.1)).isNone then
      let S' := xs.zipIdx.foldl
        (fun S p ↦ S.insert (.agent α, p.1.1) ⟨g.next + p.2, p.1.2, false⟩) S
      some ({ S' with agents := Function.update S.agents α (some Sα') },
        { g with
          next := g.next + xs.length
          steps := g.steps.push (.chooses S.mind
            (xs.zipIdx.map fun p ↦ (g.next + p.2, (dom p.1.2).size)) (.rename Sα'.links t)) })
    else none
  | .observesEvent α e => do
    let (Sα, g) := S.agent α g
    let (t, _) ← Expr.term dom e Sα
    some ({ S with agents := Function.update S.agents α (some Sα) },
      { g with
        steps := (g.steps.push (.weighs Sα.mind t)).push (.observes Sα.mind (Sα.uncertain dom)) })
  | .knows α γ y => do
    let c ← S.entries.lookup (γ, y)
    let (Sα, g) := S.agent α g
    match γ with
    | .self =>
      let Sα' := Sα.insert (.self, y) { c with certain := true }
      some ({ S.insert (.agent α, y) c with
        agents := Function.update S.agents α (some Sα') }, g)
    | .agent β =>
      let (Sβ, g) := Sα.agent β g
      let Sβ' := Sβ.insert (.self, y) { c with certain := true }
      let Sα' : Scope A N D :=
        { Sα.insert (.agent β, y) { c with certain := true } with
          agents := Function.update Sα.agents β (some Sβ') }
      some ({ S with agents := Function.update S.agents α (some Sα') }, g)
  | .observes α β x γ y => do
    let Sα ← S.agents α
    let c ← S.entries.lookup (γ, y)
    let cα ← Sα.entries.lookup (.agent β, x)
    let _ ← Sα.agents β
    if c.dom = cα.dom ∧ cα.certain = false then
      let Sα' : Scope A N D :=
        { Sα.insert (.agent β, x) { cα with certain := true } with
          links := (cα.index, c.index) :: Sα.links }
      some ({ S with agents := Function.update S.agents α (some Sα') },
        { g with steps := g.steps.push (.observes Sα.mind (Sα'.uncertain dom)) })
    else none
  | .snapshot .. | .forgets .. => none

/-- The **program of a model**. The mind `0` is the model's own, the axes of the model are its
first choices, and it is certain of them. The array may depend on the axes only. -/
def Model.program (M : Model A N D K) : Option (Program K) := do
  let k := M.axes.length
  let S₀ : Scope A N D :=
    ⟨0, M.axes.zipIdx.map fun p ↦ ((.self, p.1.1), ⟨p.2, p.1.2, true⟩), fun _ ↦ none, []⟩
  let (S, g) ← Stmt.steps dom M.body S₀ ⟨k, 1, #[]⟩
  let (t, deps) ← Expr.term dom M.ret S
  if deps.all (· < k) then
    some ⟨g.minds, g.steps.toList, t, M.axes.zipIdx.map fun p ↦ (p.2, (dom p.1.2).size)⟩
  else none

/-- The entries of the array of a model, in row-major order. -/
def Model.entries [Semifield K] [LinearOrder K] (M : Model A N D K) : Option (List K) :=
  (Model.program dom M).map Program.entries

mutual

/-- The expression uses only the forms that the translation has. -/
def Expr.covered : Expr A N D K → Bool
  | .lit _ | .choice _ => true
  | .op _ es => (List.finRange _).all fun i ↦ Expr.covered (es i)
  | .query _ e | .expect e => Expr.covered e
  | .imagine _ _ => false

end

/-- The statement uses only the forms that the translation has. -/
def Stmt.covered : Stmt A N D K → Bool
  | .pass => true
  | .seq s₁ s₂ => Stmt.covered s₁ && Stmt.covered s₂
  | .thinks _ s => Stmt.covered s
  | .chooses _ _ _ e | .choosesMax _ _ _ e | .choosesMany _ _ e | .observesEvent _ e =>
    Expr.covered e
  | .observes .. | .knows .. => true
  | .snapshot .. | .forgets .. => false

/-- The model uses only the statements and expressions that the translation has. -/
def Model.covered (M : Model A N D K) : Bool := Stmt.covered M.body && Expr.covered M.ret

end Memo.Core
