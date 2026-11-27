/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Notation
public import Minimemo.Examples.NaiveListener

/-!
# A model in the syntax of memo

This file writes the naive listener in Lean in the syntax of memo, and computes its array.

## Main definitions

* `Memo.NotationExample.naive`: the naive listener.

## Main results

* `Memo.NotationExample.rows_naive`: the array that the model returns.
-/

@[expose] public section

namespace Memo.NotationExample

open NaiveListener (Agent Dom Fn interp)

/-- The names of the choices of the model. The first two are its axes. -/
inductive Name
  | u | r | r_true | u_said | r_pick
  deriving DecidableEq

/-- The naive listener, as in memo. -/
def naive : Model Agent Name Dom Fn := memo% [u : U, r : R]
  listener: thinks[
    speaker: chooses(r_true in R, wpp=1),
    speaker: chooses(u_said in U, wpp=denotes(u_said, r_true))
  ]
  listener: observes [speaker.u_said] is u
  listener: chooses(r_pick in R, wpp=Pr[speaker.r_true == r_pick])
  return Pr[listener.r_pick == r]

theorem rows_naive :
    Model.rows interp naive =
      some [[1/2, 1/2, 0],
            [0,   0,   1],
            [1,   0,   0],
            [0,   1/2, 1/2]] := by
  decide +kernel

end Memo.NotationExample
