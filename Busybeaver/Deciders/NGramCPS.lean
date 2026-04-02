import Busybeaver.Basic
import Busybeaver.Reachability

/-
NGramCPS is a finite-window non-halting decider.

It approximates reachable executions by keeping a window of `n` symbols on each
side of the head together with the current head symbol and machine state. Since a
step can move the head outside this window, the decider also maintains the sets
of left and right `n`-grams that have been observed so far. When a step needs one
fresh symbol beyond the visible window, it reconstructs all possible continuations
that are consistent with those discovered `n`-grams.

The search proceeds as a bounded functional worklist algorithm. If it encounters a
halting transition, or if the expansion bound is exhausted, it returns `unknown`.
If the worklist closes under this finite approximation, the decider returns
`loops_prf` using a placeholder proof for now.
-/

open TM

structure NGramCPSConfig where
  n : ℕ
  bound : ℕ
deriving DecidableEq, Repr

abbrev NGram (s : ℕ) := Array (Symbol s)

/--
A finite view of the tape centered at the head.

Both `left` and `right` are stored in head-facing order: index `0` is the symbol
adjacent to the head, and the last entry is the farthest visible symbol on that side.
-/
structure PartialConfig (l s : ℕ) where
  left : NGram s
  head : Symbol s
  state : Label l
  right : NGram s
deriving DecidableEq, Repr

/--
The current closure search state: discovered left/right `n`-grams, all known
partial configurations, and the frontier for the current inner pass.
-/
structure SearchState (l s : ℕ) where
  leftNGrams : Array (NGram s)
  rightNGrams : Array (NGram s)
  partialConfigs : Array (PartialConfig l s)
  frontier : List (PartialConfig l s)
deriving Repr

/-- Result of the bounded finite-window search before it is mapped into `HaltM`. -/
inductive SearchResult where
  | closed
  | haltingEdge
  | timeout
deriving DecidableEq, Repr

/-- The data produced by expanding one partial configuration by one machine step. -/
structure Expansion (l s : ℕ) where
  leftNGrams : Array (NGram s)
  rightNGrams : Array (NGram s)
  successors : Array (PartialConfig l s)
deriving Repr

inductive StepResult (l s : ℕ) where
  | haltingEdge
  | advanced (expansion : Expansion l s)
deriving Repr

/--
Result of one complete inner pass over the current frontier. If either n-gram set
grew during the pass, the outer loop must restart from all known partial configs.
-/
inductive RoundResult (l s : ℕ) where
  | closed
  | haltingEdge
  | timeout
  | restart (remaining : ℕ) (state : SearchState l s)
deriving Repr

namespace NGramCPS

def insertIfNew [DecidableEq α] (as : Array α) (a : α) : Array α :=
  if a ∈ as then
    as
  else
    as.push a

def insertAllIfNew [DecidableEq α] (base extra : Array α) : Array α :=
  extra.foldl insertIfNew base

-- TODO: Consider more efficient implementations (avoid using toList)

/-- Insert a symbol next to the head and discard the farthest visible symbol. -/
def shiftInNear (a : α) (as : Array α) : Array α :=
  #[a] ++ as.pop

/-- Extend a visible prefix with one newly guessed far symbol. -/
def appendFar (as : Array α) (a : α) : Array α :=
  (as.toList ++ [a]).toArray

/--
Given a length `n - 1` prefix and a set of known `n`-grams, collect all possible
last symbols of matching `n`-grams. These symbols are the possible one-cell
extensions beyond the visible window.
-/
def matchingLastSymbols [DecidableEq α] (prefixArr : Array α) (ngrams : Array (Array α))
      (fallback : α) :
    Array α :=
  ngrams.filterMap (fun ngram =>
    if ngram.take prefixArr.size = prefixArr then
      -- TODO: We don't need fallback here since ngram always has length `n`.
      -- TODO: Migrate the code to use Vector rather than Array to statically guarantee the length.
      some (ngram.getD prefixArr.size fallback)
    else
      none)


/-- Expand a step to the right by reconstructing the unseen symbol on the right. -/
def expandRight (rightNGrams : Array (NGram s)) (cfg : PartialConfig l s) (writeSym : Symbol s)
    (nextState : Label l) : Expansion l s :=
  let newLeft := shiftInNear writeSym cfg.left
  let rightPrefix := cfg.right.drop 1
  -- TODO: No need to use default here, cfg.right always has length `n` greater than 0
  --       This should be fixed when we use Vector, and pass the condition that n is
  --       greater than 0 in the config struct.
  let newHead := cfg.right.getD 0 default
  let successors :=
    matchingLastSymbols rightPrefix rightNGrams default |>.map fun sym ↦
      {
        left := newLeft
        head := newHead
        state := nextState
        right := appendFar rightPrefix sym
      }
  {
    leftNGrams := #[newLeft]
    rightNGrams := #[]
    successors
  }

/-- Expand a step to the left by reconstructing the unseen symbol on the left. -/
def expandLeft (leftNGrams : Array (NGram s)) (cfg : PartialConfig l s) (writeSym : Symbol s)
    (nextState : Label l) : Expansion l s :=
  let newRight := shiftInNear writeSym cfg.right
  let leftPrefix := cfg.left.drop 1
  let newHead := cfg.left.getD 0 default
  let successors :=
    matchingLastSymbols leftPrefix leftNGrams default |>.map fun sym ↦
      {
        left := appendFar leftPrefix sym
        head := newHead
        state := nextState
        right := newRight
      }
  {
    leftNGrams := #[]
    rightNGrams := #[newRight]
    successors
  }

def stepPartialConfig (M : Machine l s) (leftNGrams rightNGrams : Array (NGram s))
    (cfg : PartialConfig l s) : StepResult l s :=
  match M.get cfg.state cfg.head with
  | .halt => .haltingEdge
  | .next writeSym .right nextState => .advanced (expandRight rightNGrams cfg writeSym nextState)
  | .next writeSym .left nextState => .advanced (expandLeft leftNGrams cfg writeSym nextState)

/--
Insert only genuinely new successor configurations and enqueue them for future
expansion during the current inner pass. This keeps the worklist search
functional while still behaving like a standard visited-set traversal.
-/
def addSuccessors (known : Array (PartialConfig l s)) (frontier : List (PartialConfig l s))
    (successors : Array (PartialConfig l s)) :
    Array (PartialConfig l s) × List (PartialConfig l s) :=
  successors.foldl
    (fun (acc : Array (PartialConfig l s) × List (PartialConfig l s)) cfg =>
      let (knownAcc, frontierAcc) := acc
      if cfg ∈ knownAcc  then
        acc
      else
        (knownAcc.push cfg, cfg :: frontierAcc))
    (known, frontier)

/--
Process one full inner pass over the current frontier. If either n-gram set grows,
the caller must restart from all known partial configs because older expansions may
now yield additional successors.
-/
def runRound (M : Machine l s) : ℕ → SearchState l s → Bool → RoundResult l s
  | bound, state, changed =>
      match state.frontier with
      | [] =>
          if changed then
            .restart bound {
              state with
              frontier := state.partialConfigs.toList
            }
          else
            .closed
      | cfg :: rest =>
          match bound with
          | 0 => .timeout
          | bound' + 1 =>
              match stepPartialConfig M state.leftNGrams state.rightNGrams cfg with
              | .haltingEdge => .haltingEdge
              | .advanced expansion =>
                  let nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams
                  let nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams
                  let (nextConfigs, nextFrontier) :=
                    addSuccessors state.partialConfigs rest expansion.successors
                  let changed' :=
                    changed ||
                    nextLeft.size ≠ state.leftNGrams.size ||
                    nextRight.size ≠ state.rightNGrams.size
                  runRound M bound' {
                    leftNGrams := nextLeft
                    rightNGrams := nextRight
                    partialConfigs := nextConfigs
                    frontier := nextFrontier
                  } changed'

/--
This method implements the full search procedure. In particular it runs multiple rounds while
the n-gram sets keep growing, and it returns `timeout` if the expansion bound is exhausted
before the search closes or finds a halting edge.

`rounds` is the total number of rounds, which limits how many times we restart from all known
partial configs when the n-gram sets grow. This is mostly unused, however it is useful to let
lean know that the search will definitely terminate after a finite number of rounds, even though
the reason for termination will be that the search ends (.closed / .haltingEdge) or that the
inner expansion budget is exhausted (.timeout) rather than that we hit the round limit.
-/
def runSearchOuter (M : Machine l s) : ℕ → ℕ → SearchState l s → SearchResult
  | 0, _, _ => .timeout
  | rounds + 1, remaining, state =>
      match runRound M remaining state false with
      | .closed => .closed
      | .haltingEdge => .haltingEdge
      | .timeout => .timeout
      | .restart remaining' state' => runSearchOuter M rounds remaining' state'

def runSearch (M : Machine l s) (bound : ℕ) (state : SearchState l s) : SearchResult :=
  runSearchOuter M bound bound state

/-- Initial search state for the blank tape and default start state. -/
def initialState (cfg : NGramCPSConfig) : SearchState l s :=
  let blankNGram : NGram s := Array.replicate cfg.n default
  let firstConfig : PartialConfig l s := {
    left := blankNGram
    head := default
    state := default
    right := blankNGram
  }
  {
    leftNGrams := #[blankNGram]
    rightNGrams := #[blankNGram]
    partialConfigs := #[firstConfig]
    frontier := [firstConfig]
  }

end NGramCPS

def nGramCPSDecider (cfg : NGramCPSConfig) (M : Machine l s) : HaltM M Unit :=
  if cfg.n = 0 then
    .unknown ()
  else
    match NGramCPS.runSearch M cfg.bound (NGramCPS.initialState cfg) with
    | .closed => .loops_prf (by sorry)
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()
