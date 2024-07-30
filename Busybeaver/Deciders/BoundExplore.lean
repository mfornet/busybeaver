import Busybeaver.Basic
import Busybeaver.Reachability

open TM

/--
A decider that explores a bounded number of steps of the machine and produces a
certificate that the machine halts if it finds the end.

This is more a proof of concept that simple verifiers are possible rather that an
actual verifier.
-/
-- def boundedExplore [Inhabited $ Label l] [Inhabited $ Symbol s] (bound: ℕ): HaltM M Unit := do
--   let cur: { s // M.Reaches init s } := ⟨init, Machine.Reaches.refl⟩
--   .unknown ()
def boundedExplore [Inhabited $ Label l] [Inhabited $ Symbol s] (bound: ℕ) (M: Machine l s): HaltM M Unit :=
  let rec boundedExploreCore [Inhabited $ Label l] [Inhabited $ Symbol s] (bound: ℕ) {k} (σ: { s // init -[M]{k}-> s }): HaltM M Unit := match bound with
  | 0 => .unknown ()
  | n + 1 => M.stepH σ >>= boundedExploreCore n
  boundedExploreCore bound ⟨init, Machine.Multistep.refl⟩
