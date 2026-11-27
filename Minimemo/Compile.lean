/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Program
public import Minimemo.Syntax

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
* `Memo.Expr.term dom e S g`: the term of the expression `e` in the scope `S`, with the
  choices that it depends on.
* `Memo.Stmt.steps dom s S g`: the scope after the statement `s`, with its steps added to
  `g`.
* `Memo.Model.program dom M`: the program of the model `M`, if memo accepts the model.
* `Memo.Model.size dom M`: the size of each choice of the model `M`.
* `Memo.Model.entries dom M`: the entries of the array of `M`, in row-major order.
* `Memo.Model.rows dom M`: the same entries, as rows along the last axis.
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
structure Gen (K : Type u) : Type u where
  /-- The next free number of a choice. -/
  next : ℕ
  /-- The steps so far. -/
  steps : Array (Step K)

/-- The steps with one more, and the number of the table that it adds. -/
def Gen.push {K : Type u} (g : Gen K) (s : Step K) : Gen K × ℕ :=
  ({ g with steps := g.steps.push s }, g.steps.size + 1)

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

/-- The scope without the choices at the addresses in `as`. -/
def erase (S : Scope A N D) (as : List (Ref A × N)) : Scope A N D :=
  { S with entries := S.entries.filter fun p ↦ p.1 ∉ as }

/-- The scope of the agent `α` in a scope, or the empty scope, whose belief is the table `0`. -/
def agent (S : Scope A N D) (α : A) : Scope A N D :=
  (S.agents α).getD ⟨0, [], fun _ ↦ none, []⟩

/-- The scope in which the scope of the agent `α` is `Sα`. -/
def setAgent (S : Scope A N D) (α : A) (Sα : Scope A N D) : Scope A N D :=
  { S with agents := Function.update S.agents α (some Sα) }

/-- The choice that a choice of the scope equals outside. -/
def link (S : Scope A N D) (i : ℕ) : ℕ := (S.links.lookup i).getD i

end Scope

/-- The values of a family of options, if every one of them is defined. -/
def allSome {k : ℕ} {β : Type*} (o : Fin k → Option β) : Option (Fin k → β) :=
  if h : ∀ i, (o i).isSome then some fun i ↦ (o i).get (h i) else none

variable (dom : D → Domain K)

mutual

/-- The sizes of the choices that an expression imagines, in the order of their numbers. -/
def Expr.sizes : Expr A N D K → List ℕ
  | .lit _ | .choice _ => []
  | .op _ es => (List.finRange _).flatMap fun i ↦ Expr.sizes (es i)
  | .query _ e | .expect e => Expr.sizes e
  | .imagine s e => Stmt.sizes s ++ Expr.sizes e

/-- The sizes of the choices that a statement makes, with those that its expressions imagine, in
the order of their numbers. -/
def Stmt.sizes : Stmt A N D K → List ℕ
  | .chooses _ _ X e | .choosesMax _ _ X e => (dom X).size :: Expr.sizes e
  | .choosesMany _ xs e => (xs.map fun p ↦ (dom p.2).size) ++ Expr.sizes e
  | .observesEvent _ e => Expr.sizes e
  | .thinks _ s => Stmt.sizes s
  | .seq s₁ s₂ => Stmt.sizes s₁ ++ Stmt.sizes s₂
  | .observes .. | .knows .. | .snapshot .. | .forgets .. | .pass => []

end

mutual

/-- The **term of an expression** in a scope, with the choices that it depends on. -/
def Expr.term (e : Expr A N D K) (S : Scope A N D) (g : Gen K) : Option (Term K × List ℕ) :=
  match e with
  | .lit r => some (.lit r, [])
  | .op f es =>
    (allSome fun i ↦ Expr.term (es i) S
      { g with next := g.next + (((List.finRange _).take i).flatMap fun j ↦
        Expr.sizes dom (es j)).length }).map fun ts ↦
      (.op f fun i ↦ (ts i).1, ((List.finRange _).flatMap fun i ↦ (ts i).2).dedup)
  | .choice x =>
    (S.entries.lookup (.self, x)).map fun c ↦
      (.val c.index (dom c.dom).size (dom c.dom).val, [c.index])
  | .query α e => do
    let Sα ← S.agents α
    let (t, deps) ← Expr.term e Sα g
    if deps.all (· ∈ Sα.certain) then some (.rename Sα.links t, (deps.map Sα.link).dedup)
    else none
  | .expect e => do
    let (t, deps) ← Expr.term e S g
    if deps.all (· ∈ S.certain) then some (t, deps)
    else some (.expect S.table (S.uncertain dom) t, S.certain)
  | .imagine s e => do
    let (S', g') ← Stmt.steps s S g
    let (t, deps) ← Expr.term e S' g'
    if deps.all fun i ↦ i ∈ S'.certain ∧ S.entries.any (·.2.index == i) then
      some ((g'.steps.toList.drop g.steps.size).foldr Term.after t, deps)
    else none
termination_by structural e

/-- The scope after a **statement**, with the steps of the statement added. -/
def Stmt.steps (s : Stmt A N D K) (S : Scope A N D) (g : Gen K) : Option (Scope A N D × Gen K) :=
  match s with
  | .pass => some (S, g)
  | .seq s₁ s₂ => do
    let (S', g') ← Stmt.steps s₁ S g
    Stmt.steps s₂ S' g'
  | .thinks α s => do
    let (Sα, g') ← Stmt.steps s (S.agent α) g
    some (S.setAgent α Sα, g')
  | .chooses α x X e => do
    let Sα := S.agent α
    let Sα' := Sα.insert (.self, x) ⟨g.next, X, true, false⟩
    let (t, deps) ← Expr.term e Sα' { g with next := g.next + 1 }
    if deps.all (· ∈ Sα'.certain) ∧ (Sα.entries.lookup (.self, x)).isNone then
      let (g', w) := g.push (.chooses S.table [(g.next, (dom X).size)] (.rename Sα'.links t))
      some ({ (S.insert (.agent α, x) ⟨g.next, X, false, false⟩).setAgent α Sα' with table := w },
        { g' with next := g.next + 1 + (Expr.sizes dom e).length })
    else none
  | .choosesMax α x X e => do
    let Sα := S.agent α
    let Sα' := Sα.insert (.self, x) ⟨g.next, X, true, false⟩
    let (t, deps) ← Expr.term e Sα' { g with next := g.next + 1 }
    if deps.all (· ∈ Sα'.certain) ∧ (Sα.entries.lookup (.self, x)).isNone then
      let (g', w) := g.push (.chooses S.table [(g.next, (dom X).size)]
        (.rename Sα'.links (.best g.next (dom X).size t)))
      some ({ (S.insert (.agent α, x) ⟨g.next, X, false, false⟩).setAgent α Sα' with table := w },
        { g' with next := g.next + 1 + (Expr.sizes dom e).length })
    else none
  | .choosesMany α xs e => do
    let Sα := S.agent α
    let Sα' := xs.zipIdx.foldl
      (fun S p ↦ S.insert (.self, p.1.1) ⟨g.next + p.2, p.1.2, true, false⟩) Sα
    let (t, deps) ← Expr.term e Sα' { g with next := g.next + xs.length }
    if deps.all (· ∈ Sα'.certain) ∧ xs.all fun p ↦ (Sα.entries.lookup (.self, p.1)).isNone then
      let S' := xs.zipIdx.foldl
        (fun S p ↦ S.insert (.agent α, p.1.1) ⟨g.next + p.2, p.1.2, false, false⟩) S
      let (g', w) := g.push (.chooses S.table
        (xs.zipIdx.map fun p ↦ (g.next + p.2, (dom p.1.2).size)) (.rename Sα'.links t))
      some ({ S'.setAgent α Sα' with table := w },
        { g' with next := g.next + xs.length + (Expr.sizes dom e).length })
    else none
  | .observes α β x γ y => do
    let Sα ← S.agents α
    let c ← S.entries.lookup (γ, y)
    let cα ← Sα.entries.lookup (.agent β, x)
    let _ ← Sα.agents β
    if c.dom = cα.dom ∧ cα.certain = false then
      let Sα' : Scope A N D :=
        { Sα.insert (.agent β, x) { cα with certain := true, given := true } with
          links := (cα.index, c.index) :: Sα.links }
      let (g', w) := g.push (.observes Sα.table (Sα'.uncertain dom))
      some (S.setAgent α { Sα' with table := w }, g')
    else none
  | .observesEvent α e => do
    let Sα := S.agent α
    let (t, _) ← Expr.term e Sα g
    let (g', w) := g.push (.weighs Sα.table t)
    let (g'', w') := g'.push (.observes w (Sα.uncertain dom))
    some (S.setAgent α { Sα with table := w' }, { g'' with next := g.next + (Expr.sizes dom e).length })
  | .knows α γ y => do
    let c ← S.entries.lookup (γ, y)
    let Sα := S.agent α
    let c' : Entry D := { c with certain := true, given := true }
    match γ with
    | .self => some ((S.insert (.agent α, y) c).setAgent α (Sα.insert (.self, y) c'), g)
    | .agent β =>
      some (S.setAgent α
        ((Sα.insert (.agent β, y) c').setAgent β ((Sα.agent β).insert (.self, y) c')), g)
  | .snapshot α β =>
    let Sα := S.agent α
    let Sβ : Scope A N D :=
      { Sα with entries := Sα.entries.map fun p ↦ (p.1, { p.2 with given := true }), links := [] }
    let Sα' := Sα.entries.foldl
      (fun S p ↦ if p.1.1 = .self then S.insert (.agent β, p.1.2) { p.2 with given := true }
        else S) Sα
    some (S.setAgent α (Sα'.setAgent β Sβ), g)
  | .forgets α xs => do
    let Sα ← S.agents α
    if xs.all fun x ↦ (Sα.entries.lookup (.self, x)).any (!·.given) ∧
        (S.entries.lookup (.agent α, x)).isSome then
      let over := (xs.filterMap fun x ↦
        (S.entries.lookup (.agent α, x)).map fun c ↦ (c.index, (dom c.dom).size)).dedup
      let (g', w) := g.push (.forgets S.table over)
      some ({ (S.erase (xs.map fun x ↦ (.agent α, x))).setAgent α
          (Sα.erase (xs.map fun x ↦ (.self, x))) with table := w }, g')
    else none
termination_by structural s

end

/-- The **program of a model**. The axes of the model are its first choices, and the model is
certain of them. The array may depend on the axes only. -/
def Model.program (M : Model A N D K) : Option (Program K) := do
  let k := M.axes.length
  let S₀ : Scope A N D :=
    ⟨0, M.axes.zipIdx.map fun p ↦ ((.self, p.1.1), ⟨p.2, p.1.2, true, false⟩), fun _ ↦ none, []⟩
  let (S, g) ← Stmt.steps dom M.body S₀ ⟨k, #[]⟩
  let (t, deps) ← Expr.term dom M.ret S g
  if deps.all (· < k) then
    some ⟨g.steps.toList, t, M.axes.zipIdx.map fun p ↦ (p.2, (dom p.1.2).size)⟩
  else none

/-- The size of each choice of a model: the sizes of its axes, then of the choices of its
statement, then of the choices that its expression imagines, in the order of their numbers. -/
def Model.size (M : Model A N D K) (i : ℕ) : ℕ :=
  ((M.axes.map fun p ↦ (dom p.2).size) ++ Stmt.sizes dom M.body ++ Expr.sizes dom M.ret).getD i 0

/-- The entries of the array of a model, in row-major order. -/
def Model.entries [Semifield K] [LinearOrder K] (M : Model A N D K) : Option (List K) :=
  (Model.program dom M).map Program.entries

/-- The rows of the array of a model, along its last axis. -/
def Model.rows [Semifield K] [LinearOrder K] (M : Model A N D K) : Option (List (List K)) :=
  (Model.program dom M).map Program.rows

end Memo
