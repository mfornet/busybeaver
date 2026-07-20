import Busybeaver.Deciders.Cyclers
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.TranslatedCyclers
import Busybeaver.Deciders.BackwardsReasoning
import Busybeaver.Deciders.NGramCPS
import Busybeaver.Deciders.RepWL
import Busybeaver.Deciders.Loop1
import Busybeaver.Deciders.BB5Table
import Busybeaver.Deciders.BB5TableEntries
import Busybeaver.Enumerate.Alg
import Busybeaver.Enumerate.Impl
import Busybeaver.TM.Table.Model

import Lean.Data.Json

/-!
# Decider pipeline

Pure decider-pipeline combinators shared by the `beaver` CLI (`Main.lean`) and
the gated value theorems (`BBTheorems/`): the `DeciderConfig` datatype
describing one decider pass, its interpretation as a proof-carrying decider,
the per-size default pipelines, and the end-to-end `compute` wrapper around
`BBCompute`. IO-specific glue (JSON config files, holdout logging, witness
emission, progress bars) stays in `Main.lean`.
-/

open TM TM.Table

instance {l s : ℕ} {M : Machine l s} : ToString (HaltM M α) where
  toString := λ
  | .unknown _ => s!"unknown"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

instance {M : Type _} [TM.Model M] {m : M} : ToString (TM.Model.HaltM m α) where
  toString := λ
  | .unknown _ => s!"unknown"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

namespace Pipeline

open Lean

/-- Run the TNF enumeration from both seeds and join the results. `undec = ∅`
feeds `Busybeaver.BBCompute.correct_complete` to certify `val`. -/
def compute (l s: ℕ) (dec: (M: Machine l s) → HaltM M Unit): Busybeaver.BBResult l s :=
  let res0 := Busybeaver.BBCompute dec (Busybeaver.BBCompute.m0RB l s)
  let res1 := Busybeaver.BBCompute dec (Busybeaver.BBCompute.m1RB l s)
  Busybeaver.BBResult.join res0 res1

deriving instance FromJson, ToJson for NGramCPSConfig
deriving instance FromJson, ToJson for NGramCPSHistoryConfig
deriving instance FromJson, ToJson for NGramCPSLRUConfig
deriving instance FromJson, ToJson for RepWLConfig

inductive DeciderConfig where
| translatedCycler : ℕ → DeciderConfig
| cycler : ℕ → DeciderConfig
| explore : ℕ → DeciderConfig
| loop1 : ℕ → DeciderConfig
| backwardsReasoning : ℕ → DeciderConfig
| nGramCPS : NGramCPSConfig → DeciderConfig
| nGramCPSHistory : NGramCPSHistoryConfig → DeciderConfig
| nGramCPSLRU : NGramCPSLRUConfig → DeciderConfig
| repWL : RepWLConfig → DeciderConfig
| bb5TableExecutable : DeciderConfig
| bb5TableAll : DeciderConfig
| bb5TableNF : DeciderConfig
deriving FromJson, ToJson

instance: ToString DeciderConfig where
  toString := λ
  | .translatedCycler n => s!"Translated cycler {n}"
  | .cycler n => s!"Cycler {n}"
  | .explore n => s!"Explore {n}"
  | .loop1 n => s!"Loop1 {n}"
  | .backwardsReasoning n => s!"Backwards Reasoning {n}"
  | .nGramCPS cfg => s!"NGram CPS n={cfg.n} bound={cfg.bound}"
  | .nGramCPSHistory cfg =>
      s!"NGram CPS history={cfg.history} left={cfg.left} right={cfg.right} bound={cfg.bound}"
  | .nGramCPSLRU cfg =>
      s!"NGram CPS LRU left={cfg.left} right={cfg.right} bound={cfg.bound}"
  | .repWL cfg =>
      s!"RepWL len={cfg.len} threshold={cfg.threshold} maxT={cfg.maxT} bound={cfg.bound}"
  | .bb5TableExecutable => "BB5 executable hardcoded table"
  | .bb5TableAll => "BB5 full hardcoded table"
  | .bb5TableNF => "BB5 normal-form hardcoded table"

def DeciderConfig.deciderModel {M : Type _} [TM.Model M] (cfg: DeciderConfig) (m : M) :
    TM.Model.HaltM m Unit := match cfg with
| .translatedCycler n => do
    let _ ← Deciders.TranslatedCyclers.translatedCyclerDecider n m
| .explore n => do
    let _ ← Deciders.BoundExplore.boundedExplore n m
| .cycler n => Deciders.Cyclers.looperDecider n m
| _ => .unknown ()

def runBB5Table (table : Deciders.BB5Table.Table) (M : Machine l s) : HaltM M Unit :=
  match l, s with
  | 4, 1 => Deciders.BB5Table.tableDecider table M
  | _, _ => .unknown ()

def runBB5TableNF (table : Deciders.BB5Table.Table) (M : Machine l s) : HaltM M Unit :=
  match l, s with
  | 4, 1 => Deciders.BB5Table.nfTableDecider table M
  | _, _ => .unknown ()

/-- Table-free interpretation of a `DeciderConfig`: like `deciderTable` but the
`.bb5Table*` passes are inert (`.unknown`). Split out so statements about sizes
that never need the hardcoded BB5 table (the `BBTheorems.bb2`–`bb4` value
theorems) do not pull the table — and hence the sporadic-machine certificates,
with their current `sorry`/`native_decide` axioms — into their constant closure. -/
def DeciderConfig.deciderTableCore (cfg: DeciderConfig) (M: Machine l s) : HaltM M Unit := match cfg with
| .backwardsReasoning n => backwardsReasoningDecider n M
| .nGramCPS cfg => nGramCPSDecider cfg M
| .nGramCPSHistory cfg => nGramCPSHistoryDecider cfg M
| .nGramCPSLRU cfg => nGramCPSLRUDecider cfg M
| .repWL cfg => Deciders.RepWL.decider cfg M
| .loop1 n => Deciders.Loop1.decider n M
| _ => TM.Table.Model.modelHaltMToTableHaltM (cfg.deciderModel M)

def DeciderConfig.deciderTable (cfg: DeciderConfig) (M: Machine l s) : HaltM M Unit := match cfg with
| .bb5TableExecutable => runBB5Table Deciders.BB5Table.Generated.executableTable M
| .bb5TableAll => runBB5Table Deciders.BB5Table.Generated.allTable M
| .bb5TableNF => runBB5TableNF Deciders.BB5Table.Generated.executableTable M
| cfg => cfg.deciderTableCore M

@[inline]
def toDecider (cfg: List DeciderConfig) (M: Machine l s): TM.Model.HaltM M Unit := do
  for d in cfg do
    d.deciderModel M

/-- Table-free variant of `toTableDecider` (see `DeciderConfig.deciderTableCore`). -/
@[inline]
def toTableDeciderCore (cfg: List DeciderConfig) (M: Machine l s): HaltM M Unit := do
  for d in cfg do
    d.deciderTableCore M

@[inline]
def toTableDecider (cfg: List DeciderConfig) (M: Machine l s): HaltM M Unit := do
  for d in cfg do
    d.deciderTable M

def firstDecision?: List DeciderConfig → (M: Machine l s) → Option (String × String)
| [], _ => none
| d :: ds, M =>
    let res := d.deciderTable M
    if HaltM.decided res then
      some (toString d, toString res)
    else
      firstDecision? ds M

/-- Like `firstDecision?`, but returns the deciding `DeciderConfig` together with the full
`HaltM` result (needed to read the halting config for tree expansion in `export`). -/
def firstDecisionFull?: List DeciderConfig → (M: Machine l s) → Option (DeciderConfig × HaltM M Unit)
| [], _ => none
| d :: ds, M =>
    let res := d.deciderTable M
    if HaltM.decided res then
      some (d, res)
    else
      firstDecisionFull? ds M

/-- Like `firstDecisionFull?` but keeps the proof-carrying `HaltM` alongside the
*name* of the decider that settled it (or `.unknown`/`none` if none did). Used to
emit witness records with provenance. Thin wrapper so the decision loop lives in
one place (`firstDecisionFull?`). -/
def decideWithProvenance (cfg: List DeciderConfig) (M: Machine l s) :
    (HaltM M Unit × Option String) :=
  match firstDecisionFull? cfg M with
  | some (d, res) => (res, some (toString d))
  | none => (.unknown (), none)

def lightDefaultConfig: List DeciderConfig := [
  .explore 130,
  .translatedCycler 300,
  .cycler 300,
  .nGramCPS { n := 1, bound := 100 },
  .nGramCPS { n := 2, bound := 200 },
  .nGramCPS { n := 3, bound := 400 }
]

def bb3DefaultConfig: List DeciderConfig :=
  lightDefaultConfig ++ [
    .nGramCPSHistory { history := 2, left := 2, right := 2, bound := 1600 }
  ]

def bb4DefaultConfig: List DeciderConfig := [
  .cycler 107,
  .nGramCPS { n := 1, bound := 100 },
  .nGramCPS { n := 2, bound := 200 },
  .nGramCPS { n := 3, bound := 400 },
  .nGramCPSHistory { history := 2, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 4, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 6, left := 3, right := 3, bound := 3200 },
  .nGramCPSHistory { history := 8, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 10, left := 4, right := 4, bound := 10000 },
  .repWL { len := 2, threshold := 3, maxT := 320, bound := 2000 },
  .repWL { len := 4, threshold := 3, maxT := 320, bound := 2000 }
]

def bb5DefaultConfig: List DeciderConfig := [
  .explore 130,
  .loop1 107,
  .nGramCPS { n := 1, bound := 400 },
  .nGramCPS { n := 2, bound := 800 },
  .nGramCPS { n := 3, bound := 400 },
  .nGramCPS { n := 4, bound := 800 },
  .explore 4100,
  .loop1 4100,
  .bb5TableExecutable,
  -- Normal-form table lookup (Coq's `NF_decider table_based_decider`): canonicalise
  -- with `TM_to_NF` then look up the table.  Cheap, and the only path for FAR / WFAR /
  -- sporadic machines reached in a non-canonical orbit representative — the heavy
  -- NGram passes below cannot decide those, so run this before them.
  .bb5TableNF,
  .repWL { len := 2, threshold := 3, maxT := 320, bound := 400 },
  .nGramCPSLRU { left := 2, right := 2, bound := 1000 },
  .nGramCPSHistory { history := 2, left := 2, right := 2, bound := 3000 },
  .nGramCPSHistory { history := 2, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 4, left := 2, right := 2, bound := 600 },
  .nGramCPSHistory { history := 4, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 6, left := 2, right := 2, bound := 3200 },
  .nGramCPSHistory { history := 6, left := 3, right := 3, bound := 3200 },
  .nGramCPSHistory { history := 8, left := 3, right := 3, bound := 1600 },
  .nGramCPSLRU { left := 3, right := 3, bound := 20000 },
  .repWL { len := 4, threshold := 2, maxT := 320, bound := 2000 },
  .repWL { len := 6, threshold := 2, maxT := 320, bound := 2000 },
  .nGramCPS { n := 4, bound := 20000 },
  -- Our NGramCPS abstraction is coarser than Coq's at equal window sizes, so the
  -- table's hardcoded params (and Coq's generic passes) underdecide for us.  These
  -- larger-window passes recover the machines that need them.
  .nGramCPS { n := 6, bound := 300000 },
  .nGramCPS { n := 8, bound := 300000 },
  .nGramCPSHistory { history := 2, left := 6, right := 6, bound := 300000 },
  .nGramCPSHistory { history := 4, left := 6, right := 6, bound := 300000 },
  .nGramCPSHistory { history := 8, left := 8, right := 8, bound := 500000 }
]

def defaultConfigFor (l s : ℕ) : List DeciderConfig :=
  if l = 2 && s = 1 then
    bb3DefaultConfig
  else if l = 3 && s = 1 then
    bb4DefaultConfig
  else if l = 4 && s = 1 then
    bb5DefaultConfig
  else
    lightDefaultConfig

end Pipeline
