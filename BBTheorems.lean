-- Root of the gated `BBTheorems` library: concrete Busy Beaver value theorems.
-- NOT part of the default build — see `BBTheorems/Common.lean` for why and how
-- to build it (`lake build BBTheorems`, or per value `lake build BBTheorems.BB2`).
import BBTheorems.Common
import BBTheorems.BB2
import BBTheorems.BB3
import BBTheorems.BB4
import BBTheorems.BB5

/- Axiom audit, printed on every build of this root module. Expected for
`bb2`–`bb4`: `propext`, `Classical.choice`, `Quot.sound`, plus the theorem's own
`native_decide` axiom. `bb5` additionally inherits the axioms of the hardcoded
table's sporadic certificates — currently `sorryAx` (Skelet #1) and the
table-internal `native_decide` axioms. -/
#print axioms BBTheorems.bb2
#print axioms BBTheorems.bb3
#print axioms BBTheorems.bb4
#print axioms BBTheorems.bb5
