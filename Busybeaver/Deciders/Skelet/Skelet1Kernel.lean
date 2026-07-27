import Busybeaver.Deciders.Skelet.Skelet1Final
import Busybeaver.Deciders.Skelet.Skelet1Backend

/-! Kernel-only Skelet #1 verification backed by the generated checkpoint graph. -/

namespace Deciders.Skelet.Skelet1.Kernel

open TM.Table

theorem nonhalt : ¬ M.halts (default : Config 4 1) :=
  Cert.nonhalt

def backend : ProofBackend := ⟨nonhalt⟩

end Deciders.Skelet.Skelet1.Kernel
