module

import Minimemo.Model
import Mathlib.Algebra.Order.Field.Rat

open Memo
open scoped Memo

namespace MinimemoTest

inductive Agent | a | b deriving DecidableEq
inductive Name | x | y | z deriving DecidableEq
inductive Dom | X deriving DecidableEq
inductive Fn : ℕ → Type

/-- One domain with the values 0, 1 and 2, and no outside functions. -/
def interp : Interp Dom Fn ℚ := .ofField (fun _ ↦ ⟨3, fun j ↦ j⟩) fun f _ ↦ nomatch f

/-- An agent who knows `x` chooses `y`, three times as likely to be `x` as each other value. -/
def model : Model Agent Name Dom Fn where
  axes := [(.x, .X)]
  body :=
    .knows .a .self .x ;;
    .chooses .a .y .X
      (.prim .add ![.lit 1, .prim .mul ![.lit 2, .prim .eq ![.choice .y, .choice .x]]])
  ret := .expect (.prim .eq ![.query .a (.choice .y), .choice .x])

example : Model.rows interp model = some [[3/5, 3/5, 3/5]] := by decide +kernel
example : Model.entries interp model = some [3/5, 3/5, 3/5] := by decide +kernel

/-- The same choice made greedily: the agent always chooses `x`. -/
def greedy : Model Agent Name Dom Fn :=
  { model with
    body := .knows .a .self .x ;; .choosesMax .a .y .X (.prim .eq ![.choice .y, .choice .x]) }

example : Model.rows interp greedy = some [[1, 1, 1]] := by decide +kernel

/-- A choice that is made twice is not a model. -/
def repeated : Model Agent Name Dom Fn :=
  { model with body := .chooses .a .y .X (.lit 1) ;; .chooses .a .y .X (.lit 1) }

example : (Model.program repeated).isNone = true := by decide +kernel

/-- A weight that the agent is uncertain of is not a model. -/
def uncertain : Model Agent Name Dom Fn :=
  { model with
    body := .thinks .a (.chooses .b .z .X (.lit 1)) ;;
      .chooses .a .y .X (.query .b (.choice .z)) }

example : (Model.program uncertain).isNone = true := by decide +kernel

end MinimemoTest
