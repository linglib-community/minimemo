module

import Minimemo.Table
import Mathlib.Algebra.Order.Field.Rat

open Memo Memo.Table

namespace Memo.Test

/-- The variable 0 has three positions and the variable 1 has two; every other variable has two. -/
def size (i : ℕ) : ℕ := if i = 0 then 3 else 2

/-- A weight on the variables 0 and 1. -/
def example₁ : Table ℚ := ofFn size [0, 1] fun σ ↦ (σ 0 + 1 : ℕ) * (σ 1 + 1 : ℕ)

/-- The product of two tables, with the operation that combines tables. -/
def mul (s t : Table ℚ) : Table ℚ :=
  op size (k := 2) (fun v ↦ v 0 * v 1) fun i ↦ if i = 0 then s else t

/-- The quotient of two tables. -/
def div (s t : Table ℚ) : Table ℚ :=
  op size (k := 2) (fun v ↦ v 0 / v 1) fun i ↦ if i = 0 then s else t

example : example₁.data = #[1, 2, 2, 4, 3, 6] := by decide +kernel
example : (example₁.sumOut size 1).data = #[3, 6, 9] := by decide +kernel
example : (example₁.sumOut size 0).data = #[6, 12] := by decide +kernel
example : ((example₁.sumOut size 0).sumOut size 1).data = #[18] := by decide +kernel
example : (div example₁ (example₁.sumOut size 1)).data = #[1/3, 2/3, 1/3, 2/3, 1/3, 2/3] := by decide +kernel
example : ((div example₁ (example₁.sumOut size 1)).sumOut size 1).data = #[1, 1, 1] := by decide +kernel
example : (mul example₁ (const 2)).data = #[2, 4, 4, 8, 6, 12] := by decide +kernel
example : (mul (ofFn size [1] fun σ ↦ (σ 1 : ℚ)) (ofFn size [0] fun σ ↦ (σ 0 : ℚ))).vars = [0, 1] := by decide +kernel
-- a sum over a variable that the table lacks adds each number to itself
example : ((example₁.sumOut size 1).sumOver size [1]).data = #[6, 12, 18] := by decide +kernel
example : (example₁.sumOver size [0, 1]).data = #[18] := by decide +kernel
example : (example₁.sumOver size [1]).data = (example₁.sumOut size 1).data := by decide +kernel
-- a renamed variable keeps its numbers and takes its place in the order
example : ((ofFn size [1, 2] fun σ ↦ (10 * σ 1 + σ 2 : ℚ)).rename size [(1, 3)]).vars = [2, 3] := by decide +kernel
example : ((ofFn size [1, 2] fun σ ↦ (10 * σ 1 + σ 2 : ℚ)).rename size [(1, 3)]).data = #[0, 10, 1, 11] := by decide +kernel
example : (example₁.rename size [(5, 6)]).data = example₁.data := by decide +kernel
-- two variables with the same replacement: the table is read where they agree
example : ((ofFn size [1, 2] fun σ ↦ (10 * σ 1 + σ 2 : ℚ)).rename size [(1, 2)]).data = #[0, 11] := by decide +kernel
example : (best size 1 example₁).data = #[0, 1, 0, 1, 0, 1] := by decide +kernel

end Memo.Test
