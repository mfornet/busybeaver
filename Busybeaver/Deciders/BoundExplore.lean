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
def boundedExplore (bound: ℕ) (M: Machine l s): HaltM M { s // default -[M]{bound}-> s } :=
  let rec boundedExploreCore (left: ℕ) {k} (hk: left + k = bound) (σ: { s // init -[M]{k}-> s }):
    HaltM M { s // default -[M]{bound}-> s } := match left with
  | 0 => .unknown ⟨σ.val, by {
    simp at hk
    cases hk
    exact σ.prop
  }⟩
  | n + 1 => M.stepH σ >>= boundedExploreCore n (by {
    rw [← hk, Nat.add_comm k, Nat.add_assoc]
  })
  boundedExploreCore bound (by rfl) ⟨init, Machine.Multistep.refl⟩
