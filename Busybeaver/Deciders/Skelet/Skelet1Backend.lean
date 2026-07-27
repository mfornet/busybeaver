import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1

open TM.Table

/-- A selectable proof of the Skelet #1 non-halting result.

The native and kernel-only implementations expose the same value, so downstream
code can be shared without depending on how the proof was established.
-/
structure ProofBackend : Type where
  nonhalt : ¬ M.halts (default : Config 4 1)

end Deciders.Skelet.Skelet1
