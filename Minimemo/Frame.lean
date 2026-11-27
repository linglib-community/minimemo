/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Syntax
public import Minimemo.Tensor
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.List.AList

/-!
# Frames of mind

This file defines the frames in which memo evaluates a model.

A frame of mind belongs to an agent. It records the name of the agent; the choices the agent is
aware of, each known to the agent or uncertain; a frame for each of the other agents that this
agent has a model of; for each choice that the agent has observed or knows, the choice of the
enclosing frame that it equals; and a tensor, the probability of the uncertain choices given the
known ones.

For example, when a listener thinks that a speaker chooses a referent, the frame of the listener
has the choice of the speaker as an uncertain choice, and contains a frame of the speaker in which
that choice is the speaker's own and is known.

## Main definitions

* `Memo.Address A N`: the type `Ref A × N` of names of choices.
* `Memo.Choice D`: a domain, an axis and whether the choice is known.
* `Memo.Frame A N D K`: a frame of mind.
* `Memo.Frame.empty name`: the frame of `name` with no choices, no agents and the tensor with
  value one.
* `Memo.Value A N K`: a tensor with the set of choices that it depends on.
* `Memo.Frame.IsKnown Φ a`: the choice `a` is known in the frame `Φ`.
* `Memo.Value.IsKnown v Φ`: every choice that `v` depends on is known in the frame `Φ`.
* `Memo.Value.lift v α Φα`: the value `v` of the frame `Φα` of the agent `α`, as a value of the
  enclosing frame.

## Implementation notes

The map from addresses to choices is an association list, since the semantics sums over the axes
of the uncertain choices and so needs the list of them. The maps to frames and to addresses are
functions with values in `Option`, since the semantics only looks them up.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

universe u v w x

namespace Memo

/-- An **address** names a choice by the agent who makes it and the name of the choice. In a frame
of mind, the agent `self` is the agent whose frame it is. -/
abbrev Address (A : Type u) (N : Type v) := Ref A × N

/-- A **choice** of a frame has a domain, the axis of the tensors along which its values lie, and
a flag that says whether the agent of the frame knows its value. -/
structure Choice (D : Type w) where
  /-- The domain that the value is chosen from. -/
  dom : D
  /-- The axis along which the values of the choice lie. -/
  axis : ℕ
  /-- Whether the agent of the frame knows the value. -/
  known : Bool
  deriving DecidableEq

/-- A **choice map** gives the choice at each address that an agent is aware of. -/
abbrev ChoiceMap (A : Type u) (N : Type v) (D : Type w) := AList fun _ : Address A N ↦ Choice D

/-- A **frame of mind** of an agent has the name of the agent, the choices that the agent is aware
of, a frame for each agent that it has a model of, the choice of the enclosing frame that each
observed or known choice equals, and a tensor: the probability of the uncertain choices given the
known ones. -/
structure Frame (A : Type u) (N : Type v) (D : Type w) (K : Type x) : Type (max u v w x) where
  /-- The agent whose frame this is, as the enclosing frame names it. The frame of a model, which
  no frame encloses, has the name `self`. -/
  name : Ref A
  /-- The choices that the agent is aware of. -/
  choices : ChoiceMap A N D
  /-- The frames of the agents that the agent has a model of. -/
  agents : A → Option (Frame A N D K)
  /-- For each observed or known choice, the address in the enclosing frame of the choice that it
  equals. -/
  conds : Address A N → Option (Address A N)
  /-- The probability of the uncertain choices given the known ones. -/
  ll : Tensor K

/-- A **value** is a tensor with the set of addresses of the choices that it depends on. -/
structure Value (A : Type u) (N : Type v) (K : Type x) where
  /-- The tensor of the value. -/
  tensor : Tensor K
  /-- The addresses of the choices that the value depends on. -/
  deps : Finset (Address A N)

variable {A : Type u} {N : Type v} {D : Type w} {K : Type x}

/-- The **empty frame** of an agent has no choices and no agents, and its tensor has the value
one. -/
def Frame.empty [One K] (name : Ref A) : Frame A N D K :=
  ⟨name, ∅, fun _ ↦ none, fun _ ↦ none, .scalar 1⟩

variable [DecidableEq A] [DecidableEq N]

namespace ChoiceMap

/-- The choice at the address `a` **is known** in a choice map if the map has a choice there and
its flag says so. -/
def IsKnown (χ : ChoiceMap A N D) (a : Address A N) : Prop :=
  (χ.lookup a).map Choice.known = some true

instance (χ : ChoiceMap A N D) : DecidablePred χ.IsKnown :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- The **uncertain axes** of a choice map are the axes of its choices that are not known, each
with the size of its domain. -/
def uncertainAxes (dom : D → Domain K) (χ : ChoiceMap A N D) : List (ℕ × ℕ) :=
  (χ.entries.filterMap fun e ↦
    if e.2.known then none else some (e.2.axis, (dom e.2.dom).size)).dedup

/-- The **known addresses** of a choice map are the addresses of its choices that are known. -/
def knownAddrs (χ : ChoiceMap A N D) : Finset (Address A N) :=
  (χ.keys.filter fun a ↦ χ.IsKnown a).toFinset

end ChoiceMap

/-- A value **is known** in a frame if every choice that it depends on is known there. -/
def Value.IsKnown (v : Value A N K) (Φ : Frame A N D K) : Prop := ∀ a ∈ v.deps, Φ.choices.IsKnown a

instance (v : Value A N K) (Φ : Frame A N D K) : Decidable (v.IsKnown Φ) :=
  inferInstanceAs (Decidable (∀ a ∈ v.deps, _))

/-- The **lift of an address** of the frame `Φα` of the agent `α` is the address of the same
choice in the enclosing frame. A choice that `α` observed or knows is the choice that it equals.
Any other choice of `α`'s own is a choice of `α` there. -/
def Frame.liftAddr (α : A) (Φα : Frame A N D K) (a : Address A N) : Option (Address A N) :=
  (Φα.conds a).orElse fun _ ↦
    match a with
    | (.self, x) => some (.agent α, x)
    | _ => none

/-- The **lift of a value** of the frame `Φα` of the agent `α` is the same tensor with the
addresses it depends on lifted to the enclosing frame. It is defined when each of them has a
lift. -/
def Value.lift (v : Value A N K) (α : A) (Φα : Frame A N D K) : Option (Value A N K) :=
  if ∀ a ∈ v.deps, (Φα.liftAddr α a).isSome then
    some ⟨v.tensor, v.deps.biUnion fun a ↦ (Φα.liftAddr α a).toFinset⟩
  else none

end Memo
