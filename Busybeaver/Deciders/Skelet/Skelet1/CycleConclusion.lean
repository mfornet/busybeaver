import Busybeaver.Deciders.Skelet.Skelet1.CycleCertificate

/-!
# Skelet #1 — final non-halting theorem

The short theorem assembly is separated from the expensive concrete
certificate so it can be edited and checked independently.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-- Skelet #1 does not halt from the blank tape. -/
theorem nonHalting : ¬ M.halts init := by
  refine multistep_nonhalt init_reach ?_
  exact doit_spec 87637654 initial doit_result

end Deciders.Skelet.Skelet1
