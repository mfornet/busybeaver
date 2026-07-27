import Busybeaver.Deciders.Skelet.Skelet1Backend

/-! Fast Skelet #1 verification using Lean's compiled evaluator.

This backend trusts `Lean.ofReduceBool`/the native compiler.  The semantic
simulator and soundness proof are shared with the kernel backend; only this
single computational equality is discharged natively. -/

namespace Deciders.Skelet.Skelet1.Native

open TM.Table

/- The symbolic simulator first sees the terminal cycle after 87,637,653
successful `fullstep`s, so one additional unit of fuel observes it. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem run : doit 87637654 initial = true := by
  native_decide

theorem nonhalt : ¬ M.halts (default : Config 4 1) :=
  Machine.halts.skip_evstep init' (doit_spec 87637654 run)

def backend : ProofBackend := ⟨nonhalt⟩

end Deciders.Skelet.Skelet1.Native
