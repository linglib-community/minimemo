/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Term

/-!
# From a model to a program

This file translates a memo model to a program on tables.

The translation reads the statements in order and keeps, for every agent's model of the world, a
scope: the number of the table that is the agent's belief, the choices that the agent is aware of,
each with its number and whether the agent is certain of it, and the scopes of the agents that
this agent has a model of. It computes no number. It checks that every expression is used where
the agent can compute it, and it writes the steps of the program.

Every choice has its own number: one that an agent makes, one that an agent thinks another agent
makes, and one that is made only inside an `imagine`. When the agent observes it, the agent becomes
certain of that choice, and the scope records a link from it to the choice that was observed. A
term that leaves the agent's mind, in a query or as the weight of the agent's choice, is read
through these links.

## Main definitions

* `Memo.Scope A N D`: the belief, choices and agents that a mind is aware of.
* `Memo.Expr.term e S g`: the term of the expression `e` in the scope `S`, with the
  choices that it depends on.
* `Memo.Stmt.steps s S g`: the scope after the statement `s`, with its steps added to
  `g`.
* `Memo.Error A N`: why a model is not accepted.
* `Memo.Model.program M`: the program of the model `M`, or why memo does not accept it.
-/

@[expose] public section

universe u

namespace Memo

/-- A choice in a scope has a number, a domain, a flag that says whether the agent of the scope is
certain of its value, and a flag that says whether the agent has the choice from outside, by
knowing or observing it. -/
structure Entry (D : Type u) : Type u where
  /-- The number of the choice. -/
  index : ℕ
  /-- The domain that the value is chosen from. -/
  dom : D
  /-- Whether the agent is certain of the value. -/
  certain : Bool
  /-- Whether the agent has the choice from outside. -/
  given : Bool := false

/-- A **scope** is what a mind is aware of: the table that is its belief, its choices by the agent
who makes them and their name, the scopes of the agents that it has a model of, and a link from
each choice that it has observed to the choice that it equals outside. -/
structure Scope (A N D : Type u) : Type u where
  /-- The number of the table that is the belief of the mind. -/
  table : ℕ
  /-- The choices that the mind is aware of. -/
  entries : List ((Ref A × N) × Entry D)
  /-- The scopes of the agents that the mind has a model of. -/
  agents : A → Option (Scope A N D)
  /-- The observed choices, each with the choice outside that it equals. -/
  links : List (ℕ × ℕ)

/-- The next free number of a choice and the steps so far. -/
structure Gen (D : Type u) (F : ℕ → Type u) : Type u where
  /-- The next free number of a choice. -/
  next : ℕ
  /-- The steps so far. -/
  steps : Array (Term D F)

/-- The steps with one more, and the number of the table that it adds. -/
def Gen.push {D : Type u} {F : ℕ → Type u} (g : Gen D F) (s : Term D F) : Gen D F × ℕ :=
  ({ g with steps := g.steps.push s }, g.steps.size + 1)

variable {A N D : Type u} {F : ℕ → Type u} [DecidableEq A] [DecidableEq N] [DecidableEq D]

namespace Scope

/-- The choices that the mind is certain of. -/
def certain (S : Scope A N D) : List ℕ :=
  S.entries.filterMap fun e ↦ if e.2.certain then some e.2.index else none

/-- The choices that the mind is uncertain of, each once. -/
def uncertain (S : Scope A N D) : List ℕ :=
  (S.entries.filterMap fun e ↦ if e.2.certain then none else some e.2.index).dedup

/-- The scope with the choice at `a` set to `e`. -/
def insert (S : Scope A N D) (a : Ref A × N) (e : Entry D) : Scope A N D :=
  { S with entries := (a, e) :: S.entries.filter fun p ↦ p.1 ≠ a }

/-- The scope with the choices `xs` as the mind's own, with the numbers from `n`. -/
def own (S : Scope A N D) (xs : List (N × D)) (n : ℕ) : Scope A N D :=
  xs.zipIdx.foldl (fun S p ↦ S.insert (.self, p.1.1) ⟨n + p.2, p.1.2, true, false⟩) S

/-- The scope without the choices at the addresses in `as`. -/
def erase (S : Scope A N D) (as : List (Ref A × N)) : Scope A N D :=
  { S with entries := S.entries.filter fun p ↦ p.1 ∉ as }

/-- The scope of the agent `α` in a scope. An agent of whom nothing was said has the empty scope,
whose belief is the table `0`. -/
def agent (S : Scope A N D) (α : A) : Scope A N D :=
  (S.agents α).getD ⟨0, [], fun _ ↦ none, []⟩

/-- The scope in which the scope of the agent `α` is `Sα`. -/
def setAgent (S : Scope A N D) (α : A) (Sα : Scope A N D) : Scope A N D :=
  { S with agents := Function.update S.agents α (some Sα) }

/-- The choice that a choice of the scope equals outside. -/
def link (S : Scope A N D) (i : ℕ) : ℕ := (S.links.lookup i).getD i

/-- Whether the mind has the choice with the number `i`. -/
def has (S : Scope A N D) (i : ℕ) : Bool := S.entries.any (·.2.index == i)

end Scope

/-- Why a model is not accepted. -/
inductive Error (A N : Type u) : Type u
  /-- A choice is used that the mind does not have. -/
  | unknownChoice (γ : Ref A) (x : N)
  /-- The agent `α` chooses `x`, which it has already chosen. -/
  | repeatedChoice (α : A) (x : N)
  /-- The weight of a choice of `α` depends on a choice that `α` is uncertain of. -/
  | uncertainWeight (α : A)
  /-- The value asked of `α` depends on a choice that `α` is uncertain of. -/
  | uncertainQuery (α : A)
  /-- The value of an `imagine` depends on a choice that is uncertain, or that is made inside
  it. -/
  | uncertainImagine
  /-- The value that the model returns depends on a choice other than its axes. -/
  | uncertainReturn
  /-- The choice `x` of `β` is observed to be a choice from another domain. -/
  | domainMismatch (β : A) (x : N)
  /-- The agent `α` observes the choice `x` of `β`, which it is already certain of. -/
  | alreadyCertain (α β : A) (x : N)
  /-- The agent `α` cannot forget `x`: it has no such choice of its own, or it was told it. -/
  | cannotForget (α : A) (x : N)
  /-- What the agent `α` answers, or the weight of its choice, depends on a choice that the mind
  asking has forgotten. -/
  | forgotten (α : A)
  deriving DecidableEq, Repr

/-- An optional value, or the error `e`. -/
def orError {ε β : Type*} (o : Option β) (e : ε) : Except ε β := o.elim (.error e) .ok

mutual

/-- The domains of the choices that an expression imagines, in the order of their numbers. -/
def Expr.doms : Expr A N D F → List D
  | .lit _ | .choice _ => []
  | .op _ es => (List.finRange _).flatMap fun i ↦ Expr.doms (es i)
  | .query _ e | .expect e => Expr.doms e
  | .imagine s e => Stmt.doms s ++ Expr.doms e

/-- The domains of the choices that a statement makes, with those that its expressions imagine,
in the order of their numbers. -/
def Stmt.doms : Stmt A N D F → List D
  | .chooses _ _ X e | .choosesMax _ _ X e => X :: Expr.doms e
  | .choosesMany _ xs e => xs.map (·.2) ++ Expr.doms e
  | .observesEvent _ e => Expr.doms e
  | .thinks _ s => Stmt.doms s
  | .seq s₁ s₂ => Stmt.doms s₁ ++ Stmt.doms s₂
  | .observes .. | .knows .. | .snapshot .. | .forgets .. | .pass => []

end

/-- The scope and the steps after the agent `α` makes the choices `xs` together, with the numbers
from the next free one. The term `r` is the weight, translated in the scope in which `α` has the
choices as its own; `wrap` is applied to it; and `extra` choices are made inside it. -/
def choose (S : Scope A N D) (g : Gen D F) (α : A) (xs : List (N × D)) (wrap : Term D F → Term D F)
    (extra : ℕ) (r : Except (Error A N) (Term D F × List ℕ)) :
    Except (Error A N) (Scope A N D × Gen D F) := do
  let Sα := S.agent α
  let Sα' := Sα.own xs g.next
  let (t, deps) ← r
  match xs.find? fun p ↦ (Sα.entries.lookup (.self, p.1)).isSome with
  | some p => .error (.repeatedChoice α p.1)
  | none =>
    if deps.all (· ∈ Sα'.certain) then
      let S' := xs.zipIdx.foldl
        (fun S p ↦ S.insert (.agent α, p.1.1) ⟨g.next + p.2, p.1.2, false, false⟩) S
      if !(deps.map Sα'.link).all S'.has then .error (.forgotten α) else
      let (g₁, r) := g.push (.rename Sα'.links (wrap t))
      let (g', w) := g₁.push (Term.chooses S.table (xs.zipIdx.map fun p ↦ g.next + p.2) (.ref r))
      pure ({ S'.setAgent α Sα' with table := w }, { g' with next := g.next + xs.length + extra })
    else .error (.uncertainWeight α)

mutual

/-- The **term of an expression** in a scope, with the choices that it depends on, or the reason
why the expression is not accepted. -/
def Expr.term (e : Expr A N D F) (S : Scope A N D) (g : Gen D F) :
    Except (Error A N) (Term D F × List ℕ) :=
  match e with
  | .lit q => .ok (.lit q, [])
  | .op o es =>
    let rs := fun i ↦ Expr.term (es i) S
      { g with next := g.next + (((List.finRange _).take i).flatMap fun j ↦
        Expr.doms (es j)).length }
    match (List.finRange _).find? fun i ↦ (rs i).toOption.isNone with
    | some i => rs i
    | none =>
      let ts := fun i ↦ (rs i).toOption.getD (.lit 0, [])
      .ok (.app o ((List.finRange _).map fun i ↦ (ts i).1),
        ((List.finRange _).flatMap fun i ↦ (ts i).2).dedup)
  | .choice x =>
    (orError (S.entries.lookup (.self, x)) (.unknownChoice .self x)).map fun c ↦
      (.val c.index c.dom, [c.index])
  | .query α e => do
    let Sα := S.agent α
    let (t, deps) ← Expr.term e Sα g
    if deps.all (· ∈ Sα.certain) then
      let deps' := (deps.map Sα.link).dedup
      if deps'.all S.has then pure (.rename Sα.links t, deps') else .error (.forgotten α)
    else .error (.uncertainQuery α)
  | .expect e => do
    let (t, deps) ← Expr.term e S g
    if deps.all (· ∈ S.certain) then pure (t, deps)
    else pure (Term.expect S.table S.uncertain t, S.certain)
  | .imagine s e => do
    let (S', g') ← Stmt.steps s S g
    let (t, deps) ← Expr.term e S' g'
    if deps.all fun i ↦ i ∈ S'.certain ∧ S.entries.any (·.2.index == i) then
      pure ((g'.steps.toList.drop g.steps.size).foldr Term.letE t, deps)
    else .error .uncertainImagine
termination_by structural e

/-- The scope after a **statement**, with the steps of the statement added, or the reason why the
statement is not accepted. -/
def Stmt.steps (s : Stmt A N D F) (S : Scope A N D) (g : Gen D F) :
    Except (Error A N) (Scope A N D × Gen D F) :=
  match s with
  | .pass => .ok (S, g)
  | .seq s₁ s₂ => do
    let (S', g') ← Stmt.steps s₁ S g
    Stmt.steps s₂ S' g'
  | .thinks α s => do
    let (Sα, g') ← Stmt.steps s (S.agent α) g
    pure (S.setAgent α Sα, g')
  | .chooses α x X e =>
    choose S g α [(x, X)] id (Expr.doms e).length
      (Expr.term e ((S.agent α).own [(x, X)] g.next) { g with next := g.next + 1 })
  | .choosesMax α x X e =>
    choose S g α [(x, X)] (.best g.next) (Expr.doms e).length
      (Expr.term e ((S.agent α).own [(x, X)] g.next) { g with next := g.next + 1 })
  | .choosesMany α xs e =>
    choose S g α xs id (Expr.doms e).length
      (Expr.term e ((S.agent α).own xs g.next) { g with next := g.next + xs.length })
  | .observes α β x γ y => do
    let Sα := S.agent α
    let c ← orError (S.entries.lookup (γ, y)) (.unknownChoice γ y)
    let cα ← orError (Sα.entries.lookup (.agent β, x)) (.unknownChoice (.agent β) x)
    if c.dom ≠ cα.dom then .error (.domainMismatch β x)
    else if cα.certain then .error (.alreadyCertain α β x)
    else
      let Sα' : Scope A N D :=
        { Sα.insert (.agent β, x) { cα with certain := true, given := true } with
          links := (cα.index, c.index) :: Sα.links }
      let (g', w) := g.push (Term.observes Sα.table Sα'.uncertain)
      pure (S.setAgent α { Sα' with table := w }, g')
  | .observesEvent α e => do
    let Sα := S.agent α
    let (t, _) ← Expr.term e Sα g
    let (g', w) := g.push (Term.weighs Sα.table t)
    let (g'', w') := g'.push (Term.observes w Sα.uncertain)
    pure (S.setAgent α { Sα with table := w' },
      { g'' with next := g.next + (Expr.doms e).length })
  | .knows α γ y => do
    let c ← orError (S.entries.lookup (γ, y)) (.unknownChoice γ y)
    let Sα := S.agent α
    let c' : Entry D := { c with certain := true, given := true }
    match γ with
    | .self => pure ((S.insert (.agent α, y) c).setAgent α (Sα.insert (.self, y) c'), g)
    | .agent β =>
      pure (S.setAgent α
        ((Sα.insert (.agent β, y) c').setAgent β ((Sα.agent β).insert (.self, y) c')), g)
  | .snapshot α β =>
    let Sα := S.agent α
    let Sβ : Scope A N D :=
      { Sα with entries := Sα.entries.map fun p ↦ (p.1, { p.2 with given := true }), links := [] }
    let Sα' := Sα.entries.foldl
      (fun S p ↦ if p.1.1 = .self then S.insert (.agent β, p.1.2) { p.2 with given := true }
        else S) Sα
    .ok (S.setAgent α (Sα'.setAgent β Sβ), g)
  | .forgets α xs => do
    let Sα := S.agent α
    match xs.find? fun x ↦ !((Sα.entries.lookup (.self, x)).any (!·.given) &&
        (S.entries.lookup (.agent α, x)).isSome) with
    | some x => .error (.cannotForget α x)
    | none =>
      let over := (xs.filterMap fun x ↦ (S.entries.lookup (.agent α, x)).map (·.index)).dedup
      let (g', w) := g.push (Term.forgets S.table over)
      pure ({ (S.erase (xs.map fun x ↦ (.agent α, x))).setAgent α
          (Sα.erase (xs.map fun x ↦ (.self, x))) with table := w }, g')
termination_by structural s

end

/-- The **program of a model**, or the reason why memo does not accept the model. The axes of the
model are its first choices, and the model is certain of them. The array may depend on the axes
only. -/
def Model.program (M : Model A N D F) : Except (Error A N) (Program D F) := do
  let k := M.axes.length
  let S₀ : Scope A N D :=
    ⟨0, M.axes.zipIdx.map fun p ↦ ((.self, p.1.1), ⟨p.2, p.1.2, true, false⟩), fun _ ↦ none, []⟩
  let (S, g) ← Stmt.steps M.body S₀ ⟨k, #[]⟩
  let (t, deps) ← Expr.term M.ret S g
  if deps.all (· < k) then
    pure ⟨M.axes.map (·.2) ++ Stmt.doms M.body ++ Expr.doms M.ret, g.steps.toList, t,
      List.range k⟩
  else .error .uncertainReturn

end Memo
