import Busybeaver.Deciders.NGramCPS.ClosedSetProof

open TM

def nGramCPSDecider (cfg : NGramCPSConfig) (M : Machine l s) : HaltM M Unit :=
  if hcfg : cfg.n = 0 then
    .unknown ()
  else
    match hSearch : NGramCPS.runSearch M cfg.bound (NGramCPS.initialState cfg) with
    | .closed _ => .loops_prf (NGramCPS.closedResult_gives_closedSet cfg hcfg hSearch).nonHalting
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()
