import Busybeaver.Deciders.Skelet.Skelet1.CycleCore

/-!
# Skelet #1 — concrete reflective certificate

This leaf module contains only the large reflective computation.  Keeping the
certificate separate means edits to the final theorem assembly do not trigger
another 87,637,654-step evaluation.
-/

namespace Deciders.Skelet.Skelet1

/-- The reflective accelerated run, using the first successful bound. -/
lemma doit_result : doit 87637654 initial = true := by
  native_decide

end Deciders.Skelet.Skelet1
