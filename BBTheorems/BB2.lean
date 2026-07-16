import BBTheorems.Common

/-! # BB(2,2) = 6 -/

open TM TM.Table Pipeline

namespace BBTheorems

theorem bb2_spec : ResultSpec 1 1 5 (toTableDeciderCore lightDefaultConfig) := by
  native_decide

/-- `BB(2,2)` in the library convention (steps to the pre-halt configuration). -/
theorem bb2 : Busybeaver 1 1 = 5 := bb2_spec.busybeaver one_ne_zero

/-- `BB(2,2) = 6` in the literature convention (the halting transition counts). -/
theorem bb2_literature : Busybeaver 1 1 + 1 = 6 := by rw [bb2]

end BBTheorems
