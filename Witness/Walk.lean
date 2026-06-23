import Busybeaver
import Witness.Store

/-!
# Witness walk

The shared IO enumeration skeleton behind both witness modes. It mirrors the
recursion of `TM.Busybeaver.BBCompute` (start machine → classify → on halt,
expand `next_machines` at the halt cell; on loop, prune; on unknown, hold out)
but runs in honest `IO`, parameterized by a `classify` callback:

* **emit mode**  — `classify` runs the real (proven) deciders and writes each
  visited node to the `Store`; the verified pure `BBCompute` is what actually
  certifies the printed answer, this walk only populates the witness.
* **trusted mode** — `classify` looks the machine up in the `Store` (with a
  fallback for misses).

This is the *unverified* tooling layer (see `memory/witness-store.md`): it builds
no Lean proof. The classifiers live in `Main` because they depend on the CLI's
`DeciderConfig`; this module stays decider-agnostic.
-/

open TM TM.Table TM.Busybeaver

namespace Witness

/-- What classifying a single machine yields. `steps` is the *actual* halting step
count (so the max over a run is exactly the BB value); `state`/`symbol` are the
halt cell, used to expand children. -/
inductive Outcome where
  | halt (state : Nat) (symbol : Nat) (steps : Nat)
  | nonhalt
  | unknown
deriving Repr, Inhabited

/-- Running result of a walk: the BB value (max actual halt steps) and the codes
of the machines left undecided. -/
structure WalkResult where
  bbValue : Nat := 0
  holdouts : Array String := #[]
deriving Inhabited

def WalkResult.join (a b : WalkResult) : WalkResult :=
  { bbValue := max a.bbValue b.bbValue, holdouts := a.holdouts ++ b.holdouts }

/-- Rebuild a `Fin (bound+1)` from a stored `Nat`. Total via `mod`; exact whenever
the value was in range (which it always is, since it came from a real `Label`/
`Symbol`). -/
private def toFin (n bound : Nat) : Fin (bound + 1) :=
  ⟨n % (bound + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The shared walk. `classify M` decides what `M` is (and, in emit mode, records
it); on `halt` we expand the children that fill the halt cell, exactly as
`BBCompute` does. `partial` because termination mirrors `BBCompute`'s
`n_halting_trans` measure, which we don't re-prove here. -/
unsafe def walk {l s : ℕ} (classify : Machine l s → IO Outcome)
    (M : Machine l s) : IO WalkResult := do
  match ← classify M with
  | .nonhalt => return {}
  | .unknown => return { holdouts := #[reprStr M] }
  | .halt state symbol steps =>
      let base : WalkResult := { bbValue := steps }
      if M.n_halting_trans ≤ 1 then
        return base
      else
        -- `Multiset` has no computable ordered iteration; `Quot.unquot` extracts
        -- the underlying list (unsafe), the same device `Main.save_to_file` uses.
        let children := Quot.unquot (next_machines M (toFin state l) (toFin symbol s)).val
        let mut acc := base
        for child in children do
          acc := acc.join (← walk classify child)
        return acc

/-- Walk both canonical roots (`0RB…`, `1RB…`) and join, mirroring `Main.compute`. -/
unsafe def walkRoots {l s : ℕ} (classify : Machine l s → IO Outcome) : IO WalkResult := do
  let r0 ← walk classify (BBCompute.m0RB l s)
  let r1 ← walk classify (BBCompute.m1RB l s)
  return r0.join r1

/-- Parallel walk, mirroring `BBComputeP`'s strategy: above `paraDepth` halting
transitions, each child subtree is spawned as its own `Task` and joined; below
it, the subtree runs serially inside the current task. Recovers the multi-core
parallelism that the verified `BBComputeP` walk has (and that the serial `walk`
threw away). Writes performed by `classify` must be thread-safe — `Store.put` is
(it holds `writeLock`). -/
unsafe def walkPar {l s : ℕ} (classify : Machine l s → IO Outcome) (paraDepth : Nat)
    (M : Machine l s) : IO WalkResult := do
  match ← classify M with
  | .nonhalt => return {}
  | .unknown => return { holdouts := #[reprStr M] }
  | .halt state symbol steps =>
      let base : WalkResult := { bbValue := steps }
      if M.n_halting_trans ≤ 1 then
        return base
      else
        let children := Quot.unquot (next_machines M (toFin state l) (toFin symbol s)).val
        if M.n_halting_trans > paraDepth then
          let tasks ← children.mapM (fun c => IO.asTask (walkPar classify paraDepth c))
          let mut acc := base
          for t in tasks do
            acc := acc.join (← IO.ofExcept t.get)
          return acc
        else
          let mut acc := base
          for c in children do
            acc := acc.join (← walkPar classify paraDepth c)
          return acc

/-- Parallel version of `walkRoots`: the two roots run as concurrent tasks too. -/
unsafe def walkRootsPar {l s : ℕ} (classify : Machine l s → IO Outcome)
    (paraDepth : Nat := 3) : IO WalkResult := do
  let t0 ← IO.asTask (walkPar classify paraDepth (BBCompute.m0RB l s))
  let t1 ← IO.asTask (walkPar classify paraDepth (BBCompute.m1RB l s))
  let r0 ← IO.ofExcept t0.get
  let r1 ← IO.ofExcept t1.get
  return r0.join r1

end Witness
