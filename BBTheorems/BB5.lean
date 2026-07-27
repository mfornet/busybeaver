import BBTheorems.Common
import Busybeaver.Deciders.Skelet.Skelet1Native

/-! # BB(5,2) = 47,176,870

**Very expensive**: the `native_decide` evaluation runs the full BB(5,2)
pipeline over the whole TNF enumeration (the same computation as
`lake exe beaver 5 2 --verify`) — expect **hours** of single-module build time.

This theorem intentionally selects the fast native-evaluation Skelet #1
backend. The separately gated `Skelet1Kernel` target checks the same table
proof using only kernel-checked checkpoints.
-/

open TM TM.Table Pipeline

namespace BBTheorems

theorem bb5_spec : ResultSpec 4 1 47176869
    (toTableDecider Deciders.Skelet.Skelet1.Native.backend bb5DefaultConfig) := by
  native_decide

/-- `BB(5,2)` in the library convention (steps to the pre-halt configuration). -/
theorem bb5 : Busybeaver 4 1 = 47176869 := bb5_spec.busybeaver four_ne_zero

/-- `BB(5,2) = 47,176,870` in the literature convention (the halting transition
counts). -/
theorem bb5_literature : Busybeaver 4 1 + 1 = 47176870 := by rw [bb5]

end BBTheorems
