import Busybeaver.Deciders.NGramCPS.ClosedSetProof
import Busybeaver.Deciders.NGramCPS.Generic.Projection

open TM.Table

def nGramCPSDecider (cfg : NGramCPSConfig) (M : Machine l s) : HaltM M Unit :=
  if hcfg : cfg.n = 0 then
    .unknown ()
  else
    match hSearch : NGramCPS.runSearch M cfg.bound (NGramCPS.initialState cfg) with
    | .closed _ => .loops_prf (NGramCPS.closedResult_gives_closedSet cfg hcfg hSearch).nonHalting
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()

private theorem nGramCPSHistoryClosed_nonHalting
    (cfg : NGramCPSHistoryConfig) (M : Machine l s)
    (hSearch : NGramCPS.Generic.runHistory cfg M = .closed state) :
    ¬M.halts init := by
  unfold NGramCPS.Generic.runHistory at hSearch
  split at hSearch
  · simp at hSearch
  · rename_i hcond
    have hnl : cfg.left ≠ 0 := by intro h; simp [h] at hcond
    have hnr : cfg.right ≠ 0 := by intro h; simp [h] at hcond
    exact NGramCPS.Generic.nonHalting_of_closedResult NGramCPS.Generic.πfst
      (NGramCPS.Generic.historyTransition_simulates cfg.history M) hnl hnr hSearch

def nGramCPSHistoryDecider (cfg : NGramCPSHistoryConfig) (M : Machine l s) : HaltM M Unit :=
  if cfg.left = 0 || cfg.right = 0 then
    .unknown ()
  else
    match hSearch : NGramCPS.Generic.runHistory cfg M with
    | .closed _ => .loops_prf (nGramCPSHistoryClosed_nonHalting cfg M hSearch)
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()

private theorem nGramCPSLRUClosed_nonHalting
    (cfg : NGramCPSLRUConfig) (M : Machine l s)
    (hSearch : NGramCPS.Generic.runLRU cfg M = .closed state) :
    ¬M.halts init := by
  unfold NGramCPS.Generic.runLRU at hSearch
  split at hSearch
  · simp at hSearch
  · rename_i hcond
    have hnl : cfg.left ≠ 0 := by intro h; simp [h] at hcond
    have hnr : cfg.right ≠ 0 := by intro h; simp [h] at hcond
    exact NGramCPS.Generic.nonHalting_of_closedResult NGramCPS.Generic.πfst
      (NGramCPS.Generic.lruTransition_simulates M) hnl hnr hSearch

def nGramCPSLRUDecider (cfg : NGramCPSLRUConfig) (M : Machine l s) : HaltM M Unit :=
  if cfg.left = 0 || cfg.right = 0 then
    .unknown ()
  else
    match hSearch : NGramCPS.Generic.runLRU cfg M with
    | .closed _ => .loops_prf (nGramCPSLRUClosed_nonHalting cfg M hSearch)
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()
