/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Frame
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# The semantics of memo

This file defines the value of an expression, the effect of a statement and the array that a
model returns.

An expression has a value in a frame of mind. A statement takes a frame and the number of the next
free axis to a new frame and a new number. A model returns the tensor of its expression in the
frame that its statement leaves.

## Main definitions

* `Memo.eval dom e Φ n`: the value of the expression `e` in the frame `Φ`, if it has one.
* `Memo.run dom s Φ n`: the frame and the next free axis after the statement `s`, if it can run.
* `Memo.Model.frame M`: the frame in which the model `M` starts, where its axes are known.
* `Memo.infer dom M`: the tensor that the model `M` returns, if it returns one.
* `Memo.Model.ref dom M vs`: the value of a reference to the model `M` at the values `vs`.
* `Memo.Model.entries dom M`: the entries of the array that `M` returns, in row-major order.

## Main results

* `Memo.eval_op₁`: the value of an operator of one argument applied to an expression.
* `Memo.run_chooses_mul`: a choice with weight `c * e`, for a nonzero number `c`, has the same
  effect as the choice with weight `e`.

## Implementation notes

The definitions follow the semantics figure of the memo paper, one case for each rule, and each
case names its rule. The cases for `knows` and `observes_event`, which the figure does not have, follow memo. For
`knows`, the agent's frame gets the choice as a known choice on the axis that it has in the
current frame. For `observes_event`, the tensor of the agent's frame is multiplied by the value of
the expression and divided by its sum over the uncertain choices. The figure writes the rules as equations with premises. Here they are
functions with values in `Option`, and the value is `none` when a premise fails. A frame that the
figure writes as a tuple of a choice map, an agent map, a condition map and a tensor is a `Frame`.

The definitions make these choices.

* The expectation `E[e]` sums over the axes of all the uncertain choices of the frame.
* Axes are numbered from zero. The axes of a model with `k` axes are `0` to `k - 1`, and the next
  free axis is `k`.
* The numbers are in a semifield `K`, in which a quotient by zero is zero.
* The meaning of a domain is given by a function `dom` from the names of domains.

The definitions are computable: over the rational numbers, `infer` evaluates a model. The names of
agents, choices and domains and the numbers are in one universe, so that frames and values are too
and the cases can be written in the `Option` monad.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

universe u

namespace Memo

variable {A N D K : Type u}

/-- The values of a family of options, if every one of them is defined. -/
def allSome {k : ℕ} {β : Type*} (o : Fin k → Option β) : Option (Fin k → β) :=
  if h : ∀ i, (o i).isSome then some fun i ↦ (o i).get (h i) else none

theorem allSome_eq_some {k : ℕ} {β : Type*} {o : Fin k → Option β} {b : Fin k → β} :
    allSome o = some b ↔ ∀ i, o i = some (b i) := by
  unfold allSome
  split_ifs with h
  · simp only [Option.some.injEq, funext_iff]
    exact forall_congr' fun i ↦
      ⟨fun hb ↦ hb ▸ (Option.some_get _).symm, fun hb ↦ by simp [hb]⟩
  · refine iff_of_false (by simp) fun hb ↦ h fun i ↦ ?_
    simp [hb i]

variable [DecidableEq A] [DecidableEq N] [DecidableEq D] [Semifield K] (dom : D → Domain K)

mutual

/-- The **value** of an expression in a frame, when `n` is the next free axis. -/
def eval (e : Expr A N D K) (Φ : Frame A N D K) (n : ℕ) : Option (Value A N K) :=
  match e with
  -- E-LITERAL
  | .lit r => some ⟨.scalar r, ∅⟩
  -- E-OP
  | .op f es =>
    (allSome fun i ↦ eval (es i) Φ n).map fun vs ↦
      ⟨fun σ ↦ f fun i ↦ (vs i).tensor σ, Finset.univ.biUnion fun i ↦ (vs i).deps⟩
  -- E-CHOICE
  | .choice x =>
    (Φ.choices.lookup (.self, x)).map fun c ↦ ⟨.basis (dom c.dom).val c.axis, {(.self, x)}⟩
  -- E-QUERY
  | .query α e => do
    let Φα ← Φ.agents α
    let v ← eval e Φα n
    if v.IsKnown Φα then v.lift α Φα else none
  -- E-EXPECTATION
  | .expect e => do
    let v ← eval e Φ n
    some ⟨Tensor.sum (Φ.choices.uncertainAxes dom) (v.tensor * Φ.ll), Φ.choices.knownAddrs⟩
  -- E-IMAGINE
  | .imagine s e => do
    let (Φ', n') ← run s Φ n
    let v ← eval e Φ' n'
    if v.IsKnown Φ' then some v else none
termination_by structural e

/-- The **effect** of a statement on a frame and on the next free axis `n`. -/
def run (s : Stmt A N D K) (Φ : Frame A N D K) (n : ℕ) : Option (Frame A N D K × ℕ) :=
  match s with
  -- S-SEQ
  | .seq s₁ s₂ => do
    let (Φ', n') ← run s₁ Φ n
    run s₂ Φ' n'
  -- S-THINKS
  | .thinks α s => do
    let (Φα, n') ← run s ((Φ.agents α).getD (.empty (.agent α))) n
    some ({ Φ with agents := Function.update Φ.agents α (some Φα) }, n')
  -- S-CHOOSES
  | .chooses α x X e => do
    let Φα := (Φ.agents α).getD (.empty (.agent α))
    let Φα' : Frame A N D K := { Φα with choices := Φα.choices.insert (.self, x) ⟨X, n, true⟩ }
    let v ← eval e Φα' (n + 1)
    if v.IsKnown Φα' then
      some ({ Φ with
        choices := Φ.choices.insert (.agent α, x) ⟨X, n, false⟩
        agents := Function.update Φ.agents α (some Φα')
        ll := Φ.ll * (v.tensor / v.tensor.sumAxis n (dom X).size) }, n + 1)
    else none
  -- S-OBSERVES
  | .observes α β x γ y => do
    let Φα ← Φ.agents α
    let c ← Φ.choices.lookup (γ, y)
    let cα ← Φα.choices.lookup (.agent β, x)
    let Φβ ← Φα.agents β
    if c.dom = cα.dom ∧ cα.known = false then
      let χα : ChoiceMap A N D := Φα.choices.insert (.agent β, x) ⟨c.dom, c.axis, true⟩
      let ll := Φα.ll.swapAxes c.axis cα.axis
      let Φβ' : Frame A N D K :=
        { Φβ with choices := Φβ.choices.insert (.self, x) ⟨c.dom, c.axis, true⟩ }
      let Φα' : Frame A N D K :=
        { name := Φα.name
          choices := χα
          agents := Function.update Φα.agents β (some Φβ')
          conds := Function.update Φα.conds (.agent β, x) (some (γ, y))
          ll := ll / Tensor.sum (χα.uncertainAxes dom) ll }
      some ({ Φ with agents := Function.update Φ.agents α (some Φα') }, n)
    else none
  -- S-OBSERVES-EVENT
  | .observesEvent α e => do
    let Φα := (Φ.agents α).getD (.empty (.agent α))
    let v ← eval e Φα n
    let ll := Φα.ll * v.tensor
    let Φα' : Frame A N D K := { Φα with ll := ll / Tensor.sum (Φα.choices.uncertainAxes dom) ll }
    some ({ Φ with agents := Function.update Φ.agents α (some Φα') }, n)
  -- S-KNOWS
  | .knows α γ y => do
    let c ← Φ.choices.lookup (γ, y)
    let Φα := (Φ.agents α).getD (.empty (.agent α))
    let c' : Choice D := { c with known := true }
    match γ with
    | .self =>
      let Φα' : Frame A N D K :=
        { Φα with
          choices := Φα.choices.insert (.self, y) c'
          conds := Function.update Φα.conds (.self, y) (some (.self, y)) }
      some ({ Φ with
        choices := Φ.choices.insert (.agent α, y) c
        agents := Function.update Φ.agents α (some Φα')
        conds := Function.update Φ.conds (.agent α, y) (some (Φ.name, y)) }, n)
    | .agent β =>
      let Φβ := (Φα.agents β).getD (.empty (.agent β))
      let Φβ' : Frame A N D K :=
        { Φβ with
          choices := Φβ.choices.insert (.self, y) c'
          conds := Function.update Φβ.conds (.self, y) (some (.agent β, y)) }
      let Φα' : Frame A N D K :=
        { Φα with
          choices := Φα.choices.insert (.agent β, y) c'
          agents := Function.update Φα.agents β (some Φβ')
          conds := Function.update Φα.conds (.agent β, y) (some (.agent β, y)) }
      some ({ Φ with agents := Function.update Φ.agents α (some Φα') }, n)
termination_by structural s

end

/-- The frame in which a model starts: its axes are choices of the current agent, each known and
on the axis of its position, and the tensor has the value one. -/
def Model.frame (M : Model A N D K) : Frame A N D K :=
  { Frame.empty .self with
    choices := M.axes.zipIdx.foldr (fun p χ ↦ χ.insert (.self, p.1.1) ⟨p.1.2, p.2, true⟩) ∅ }

/-- The tensor that a model **returns**: the tensor of its expression in the frame that its
statement leaves, when that value is known there. -/
def infer (M : Model A N D K) : Option (Tensor K) :=
  (eval dom (.imagine M.body M.ret) M.frame M.axes.length).map Value.tensor

/-- The value of a **reference** to a model at given values of its axes: the entry of the array of
the model at the positions of those values, or zero if the model returns no array. -/
def Model.ref [DecidableEq K] (M : Model A N D K) (vs : List K) : K :=
  ((infer dom M).getD 0).entry (List.zipWith (fun p v ↦ (dom p.2).index v) M.axes vs)

/-- The entries of the array of a model, in row-major order. -/
def Model.entries (M : Model A N D K) : Option (List K) :=
  (infer dom M).map (·.entries (M.axes.map fun p ↦ (dom p.2).size))

variable (Φ : Frame A N D K) (n : ℕ)

theorem eval_op₁ (f : K → K) (e : Expr A N D K) :
    eval dom (.op₁ f e) Φ n =
      (eval dom e Φ n).map fun v ↦ ⟨fun σ ↦ f (v.tensor σ), v.deps⟩ := by
  rw [Expr.op₁, eval]
  cases h : eval dom e Φ n <;> simp [allSome, h]

/-- A weight matters only up to a nonzero factor: the choice with weight `c * e` has the same
effect as the choice with weight `e`. -/
theorem run_chooses_mul {c : K} (hc : c ≠ 0) (α : A) (x : N) (X : D) (e : Expr A N D K) :
    run dom (.chooses α x X (.op₁ (c * ·) e)) Φ n = run dom (.chooses α x X e) Φ n := by
  rw [run, run, eval_op₁]
  cases h : eval dom e _ (n + 1) with
  | none => rfl
  | some v =>
    have : ((fun σ ↦ c * v.tensor σ : Tensor K) /
        Tensor.sumAxis n (dom X).size fun σ ↦ c * v.tensor σ) =
        v.tensor / v.tensor.sumAxis n (dom X).size := by
      funext σ
      simp only [Pi.div_apply, Tensor.sumAxis_apply, ← Finset.mul_sum, mul_div_mul_left _ _ hc]
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, this]
    rfl

end Memo
