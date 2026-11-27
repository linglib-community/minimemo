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

example : Model.error repeated = some (.repeatedChoice .a .y) := by decide +kernel

/-- A weight that the agent is uncertain of is not a model. -/
def uncertain : Model Agent Name Dom Fn :=
  { model with
    body := .thinks .a (.chooses .b .z .X (.lit 1)) ;;
      .chooses .a .y .X (.query .b (.choice .z)) }

example : Model.error uncertain = some (.uncertainWeight .a) := by decide +kernel

/-- A model that is accepted has no error. -/
example : Model.error model = none := by decide +kernel

/-- A choice that no one made is not a model. -/
def unknown : Model Agent Name Dom Fn :=
  { model with ret := .expect (.query .a (.choice .z)) }

example : Model.error unknown = some (.unknownChoice .self .z) := by decide +kernel

/-- An agent of whom nothing was said cannot be asked. -/
def stranger : Model Agent Name Dom Fn :=
  { model with ret := .query .b (.lit 1) }

example : Model.error stranger = some (.unknownAgent .b) := by decide +kernel

/-- A model cannot return a value that depends on an agent's choice. -/
def leaks : Model Agent Name Dom Fn :=
  { model with ret := .query .a (.choice .y) }

example : Model.error leaks = some .uncertainReturn := by decide +kernel

end MinimemoTest
