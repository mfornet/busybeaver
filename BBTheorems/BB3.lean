import BBTheorems.Common

/-! # BB(3,2) = 21 -/

open TM TM.Table Pipeline

namespace BBTheorems

theorem bb3_spec : ResultSpec 2 1 20 (toTableDeciderCore bb3DefaultConfig) := by
  native_decide

/-- `BB(3,2)` in the library convention (steps to the pre-halt configuration). -/
theorem bb3 : Busybeaver 2 1 = 20 := bb3_spec.busybeaver two_ne_zero

/-- `BB(3,2) = 21` in the literature convention (the halting transition counts). -/
theorem bb3_literature : Busybeaver 2 1 + 1 = 21 := by rw [bb3]

end BBTheorems
