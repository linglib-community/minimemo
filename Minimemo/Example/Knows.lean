/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Minimemo.Example.NaiveListener

/-!
# Models with `knows`

This file writes three models that use the statement `knows` as memo programs, and computes
their arrays.

In the first model the speaker knows the referent and chooses an utterance that describes it. In
the second a listener knows the referent and thinks that the speaker knows it too. In the third
the speaker chooses the referent, and the listener knows that choice without observing it.

## Main definitions

* `Memo.Knows.speakerKnows`, `Memo.Knows.nestedKnows`, `Memo.Knows.knowsOther`: the models.

## Main results

* `Memo.Knows.rows_speakerKnows`, `Memo.Knows.rows_nestedKnows`, `Memo.Knows.rows_knowsOther`:
  the arrays that the models return.

## Implementation notes

The terms are printed from the memo source in `scripts/examples.py`. The arrays are those that
memo 1.3.3 returns for that source. The array of the third model does not depend on the
referent.
-/

@[expose] public section

namespace Memo.Knows

open NaiveListener (Agent Dom Fn interp)

/-- The names of the choices of the models. The first two are their axes. -/
inductive Name
  | u | r | rTrue | uSaid | uGuess
  deriving DecidableEq

/-- The speaker knows the referent and chooses an utterance that describes it. -/
def speakerKnows : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .knows .speaker .self .r ;;
    .chooses .speaker .uSaid .U (.call .denotes ![.choice .uSaid, .choice .r])
  ret := .expect (.prim .eq ![.query .speaker (.choice .uSaid), .choice .u])

/-- The listener knows the referent, and thinks that the speaker knows it and chooses an utterance
that describes it. The listener then guesses the utterance. -/
def nestedKnows : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .knows .listener .self .r ;;
    .thinks .listener
      (.knows .speaker .self .r ;;
      .chooses .speaker .uSaid .U (.call .denotes ![.choice .uSaid, .choice .r])) ;;
    .chooses .listener .uGuess .U
      (.expect (.prim .eq ![.query .speaker (.choice .uSaid), .choice .uGuess]))
  ret := .expect (.prim .eq ![.query .listener (.choice .uGuess), .choice .u])

/-- The speaker chooses the referent. The listener knows that choice, thinks that the speaker
chooses an utterance that describes it, and guesses the utterance. -/
def knowsOther : Model Agent Name Dom Fn where
  axes := [(.u, .U), (.r, .R)]
  body :=
    .chooses .speaker .rTrue .R (.lit 1) ;;
    .knows .listener (.agent .speaker) .rTrue ;;
    .thinks .listener
      (.chooses .speaker .uSaid .U (.call .denotes ![.choice .uSaid, .choice .rTrue])) ;;
    .chooses .listener .uGuess .U
      (.expect (.prim .eq ![.query .speaker (.choice .uSaid), .choice .uGuess]))
  ret := .expect (.prim .eq ![.query .listener (.choice .uGuess), .choice .u])

theorem rows_speakerKnows :
    Model.rows interp speakerKnows =
      some [[1/2, 1/2, 0],
            [0,   0,   1/2],
            [1/2, 0,   0],
            [0,   1/2, 1/2]] := by
  decide +kernel

theorem rows_nestedKnows :
    Model.rows interp nestedKnows =
      some [[1/2, 1/2, 0],
            [0,   0,   1/2],
            [1/2, 0,   0],
            [0,   1/2, 1/2]] := by
  decide +kernel

theorem rows_knowsOther :
    Model.rows interp knowsOther =
      some [[1/3, 1/3, 1/3],
            [1/6, 1/6, 1/6],
            [1/6, 1/6, 1/6],
            [1/3, 1/3, 1/3]] := by
  decide +kernel

end Memo.Knows
