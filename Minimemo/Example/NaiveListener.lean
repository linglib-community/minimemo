/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Semantics
public import Mathlib.Algebra.Order.Field.Rat

/-!
# The naive listener

This file writes the first model of the memo paper as a memo program with rational numbers,
computes the array that the semantics gives it, and proves that a second model returns the same
array.

There are four utterances, *green*, *pink*, *square* and *round*, and three referents, a green
square, a green circle and a pink circle. A listener thinks that a speaker chooses a referent
uniformly and then an utterance uniformly among those that describe the referent. The listener
observes the utterance and chooses a referent with weight equal to its probability that the
speaker chose that referent. The model returns the probability that the listener chooses each
referent, in an array with an axis for the utterance and an axis for the referent.

The semantics gives the model a tensor built from sums and quotients of the denotation. Its entry
at an utterance and a referent is the value of the denotation there divided by the number of
referents that the utterance describes.

In the second model the listener thinks that the speaker chooses the utterance first, with weight
the number of referents that it describes, and then a referent that it describes. The two
speakers choose in opposite orders. The listeners return the same array.

## Main definitions

* `Memo.NaiveListener.model`: the model, as a memo program.
* `Memo.NaiveListener.utteranceFirst`: the model in which the speaker chooses the utterance first.
* `Memo.NaiveListener.tensor`: the tensor that the model returns, written with the operations on
  tensors.

## Main results

* `Memo.NaiveListener.infer_model`: the semantics gives the model the tensor `tensor`.
* `Memo.NaiveListener.tensor_entry`: the entry of the tensor at an utterance and a referent is
  the denotation there divided by its sum over the referents.
* `Memo.NaiveListener.tensor_rows`: the entries are those of the array that the paper prints.
* `Memo.NaiveListener.infer_utteranceFirst`: the two models return the same array.

## Implementation notes

The results hold by computation. For `infer_model`, the choice maps, the checks that a value is
known and the numbering of axes are decidable data, and Lean evaluates them. For the entries, the
numbers are rational, and Lean evaluates the sums and quotients. The model can also be run:
`#eval (infer dom model).map (·.rows 4 3)` prints the array.

The paper writes the weight of an utterance as `1 if denotes(u, r) else 0`; here `denotes` has the
values one and zero.

## References

* K. Chandra, T. Chen, J. B. Tenenbaum and J. Ragan-Kelley, *A Domain-Specific Probabilistic
  Programming Language for Reasoning about Reasoning (Or: A Memo on memo)*
-/

@[expose] public section

namespace Memo.NaiveListener

open Tensor

/-- The agents of the model. -/
inductive Agent
  | listener | speaker
  deriving DecidableEq

/-- The names of the choices of the model. The first two are its axes. -/
inductive Name
  | u | r | rTrue | uSaid | rPick
  deriving DecidableEq

/-- The names of the domains of the model: the utterances and the referents. -/
inductive Dom
  | U | R
  deriving DecidableEq

/-- The utterances are *green*, *pink*, *square* and *round*, with the values 0 to 3. The
referents are a green square, a green circle and a pink circle, with the values 0 to 2. -/
def dom : Dom → Domain ℚ
  | .U => ⟨4, fun j ↦ j⟩
  | .R => ⟨3, fun j ↦ j⟩

/-- The **denotation** has the value one when the utterance `u` describes the referent `r`, and
zero otherwise. -/
def denotes (u r : ℚ) : ℚ :=
  if (u = 0 ∧ (r = 0 ∨ r = 1)) ∨ (u = 1 ∧ r = 2) ∨ (u = 2 ∧ r = 0) ∨ (u = 3 ∧ (r = 1 ∨ r = 2))
  then 1 else 0

/-- The operator `==` of memo: one when its arguments are equal, and zero otherwise. -/
def eq (a b : ℚ) : ℚ := if a = b then 1 else 0

/-- The model of the naive listener:
```
@memo def L[u: U, r: R]():
  listener: thinks[
    speaker: chooses(r_true in R, wpp=1),
    speaker: chooses(u_said in U, wpp=denotes(u_said, r_true)) ]
  listener: observes [speaker.u_said] is u
  listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
  return Pr[listener.r_pick == r]
```
-/
def model : Model Agent Name Dom ℚ where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .rTrue .R (.lit 1) ;;
       .chooses .speaker .uSaid .U (.op₂ denotes (.choice .uSaid) (.choice .rTrue))) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.op₂ eq (.query .speaker (.choice .rTrue)) (.choice .rPick)))
  ret := .expect (.op₂ eq (.query .listener (.choice .rPick)) (.choice .r))

/-- The weight of each utterance, on the axis 3, at each referent, on the axis 2. -/
def weightSaid : Tensor ℚ := fun σ ↦ denotes (σ 3) (σ 2)

/-- The tensor of the listener after the two choices of the speaker: the probability of the
referent and the utterance. -/
def thinks : Tensor ℚ :=
  scalar 1 * (scalar 1 / sumAxis 2 3 (scalar 1)) * (weightSaid / sumAxis 3 4 weightSaid)

/-- The tensor of the listener after it observes the utterance, which is now on the axis 0: the
probability of the referent given the utterance. -/
def observes : Tensor ℚ :=
  swapAxes 0 3 thinks / Tensor.sum [(2, 3)] (swapAxes 0 3 thinks)

/-- The weight of each referent that the listener can pick, on the axis 4. -/
def weightPick : Tensor ℚ :=
  Tensor.sum [(2, 3)] ((fun σ ↦ eq (σ 2) (σ 4)) * observes)

/-- The tensor of the observer after the choice of the listener. -/
def observer : Tensor ℚ := scalar 1 * (weightPick / sumAxis 4 3 weightPick)

/-- The tensor that the model returns. -/
def tensor : Tensor ℚ := Tensor.sum [(4, 3)] ((fun σ ↦ eq (σ 4) (σ 1)) * observer)

/-- The semantics gives the model of the naive listener the tensor `tensor`. -/
theorem infer_model : infer dom model = some tensor := rfl

/-- The entry of the tensor at an utterance and a referent is the value of the denotation there
divided by its sum over the referents. -/
theorem tensor_entry : ∀ (u : Fin 4) (r : Fin 3),
    tensor.entry [u, r] = denotes u r / ∑ t ∈ Finset.range 3, denotes u t := by
  decide +kernel

/-- The entries of the tensor are those of the array that the paper prints for the naive
listener: *green* and *round* leave two referents equally likely, and *pink* and *square* pick out
one. -/
theorem tensor_rows :
    tensor.rows 4 3 =
      [[1/2, 1/2, 0],
       [0,   0,   1],
       [1,   0,   0],
       [0,   1/2, 1/2]] := by
  decide +kernel

/-- The number of referents that the utterance `u` describes. -/
def count (u : ℚ) : ℚ := ∑ t ∈ Finset.range 3, denotes u t

/-- The model in which the listener thinks that the speaker chooses the utterance first:
```
@memo def L'[u: U, r: R]():
  listener: thinks[
    speaker: chooses(u_said in U, wpp=count(u_said)),
    speaker: chooses(r_true in R, wpp=denotes(u_said, r_true)) ]
  listener: observes [speaker.u_said] is u
  listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
  return Pr[listener.r_pick == r]
```
-/
def utteranceFirst : Model Agent Name Dom ℚ where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .thinks .listener
      (.chooses .speaker .uSaid .U (.op₁ count (.choice .uSaid)) ;;
       .chooses .speaker .rTrue .R (.op₂ denotes (.choice .uSaid) (.choice .rTrue))) ;;
    .observes .listener .speaker .uSaid .self .u ;;
    .chooses .listener .rPick .R
      (.expect (.op₂ eq (.query .speaker (.choice .rTrue)) (.choice .rPick)))
  ret := .expect (.op₂ eq (.query .listener (.choice .rPick)) (.choice .r))

/-- The model in which the speaker chooses the utterance first returns the same array as the
model in which the speaker chooses the referent first. -/
theorem infer_utteranceFirst :
    (infer dom utteranceFirst).map (·.rows 4 3) = (infer dom model).map (·.rows 4 3) := by
  decide +kernel

end Memo.NaiveListener
