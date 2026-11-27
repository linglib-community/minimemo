import Minimemo.Table
import Mathlib.Algebra.Order.Field.Rat

open Memo Memo.Table

namespace MinimemoTest

/-- A weight on two variables, 0 with three positions and 1 with two. -/
def example₁ : Table ℚ := ofFn [(0, 3), (1, 2)] fun σ ↦ (σ 0 + 1 : ℕ) * (σ 1 + 1 : ℕ)

#guard example₁.data == #[1, 2, 2, 4, 3, 6]
#guard (example₁.sumOut 1).data == #[3, 6, 9]
#guard (example₁.sumOut 0).data == #[6, 12]
#guard ((example₁.sumOut 0).sumOut 1).data == #[18]
#guard (example₁ / example₁.sumOut 1).data == #[1/3, 2/3, 1/3, 2/3, 1/3, 2/3]
#guard ((example₁ / example₁.sumOut 1).sumOut 1).data == #[1, 1, 1]
#guard (example₁ * const 2).data == #[2, 4, 4, 8, 6, 12]
#guard (ofFn [(1, 2)] (fun σ ↦ (σ 1 : ℚ)) * ofFn [(0, 3)] fun σ ↦ (σ 0 : ℚ)).vars == [(0, 3), (1, 2)]

-- a sum over a variable that the table lacks adds each number to itself
#guard ((example₁.sumOut 1).sumOver [(1, 2)]).data == #[6, 12, 18]
#guard (example₁.sumOver [(0, 3), (1, 2)]).data == #[18]
#guard (example₁.sumOver [(1, 2)]).data == (example₁.sumOut 1).data
-- a renamed variable keeps its numbers and takes its place in the order
#guard (example₁.rename [(0, 2)]).vars == [(1, 2), (2, 3)]
#guard (example₁.rename [(0, 2)]).data == #[1, 2, 3, 2, 4, 6]
#guard (example₁.rename [(5, 6)]).data == example₁.data
-- two variables with the same replacement: the table is read where they agree
#guard ((ofFn [(0, 2), (1, 2)] fun σ ↦ (10 * σ 0 + σ 1 : ℚ)).rename [(0, 1)]).data == #[0, 11]
#guard (op (k := 2) (fun v ↦ v 0 + v 1) fun i ↦ if i = 0 then example₁ else const 1).data == #[2, 3, 3, 5, 4, 7]

end MinimemoTest
