import BBTheorems.Common

/-! # BB(4,2) = 107

Expect this module to take a few minutes to build: the `native_decide`
evaluation runs the full BB(4,2) pipeline (the same computation as
`lake exe beaver 4 2 --verify`).
-/

open TM TM.Table Pipeline

namespace BBTheorems

theorem bb4_spec : ResultSpec 3 1 106 (toTableDeciderCore bb4DefaultConfig) := by
  native_decide

/-- `BB(4,2)` in the library convention (steps to the pre-halt configuration). -/
theorem bb4 : Busybeaver 3 1 = 106 := bb4_spec.busybeaver three_ne_zero

/-- `BB(4,2) = 107` in the literature convention (the halting transition counts). -/
theorem bb4_literature : Busybeaver 3 1 + 1 = 107 := by rw [bb4]

end BBTheorems
