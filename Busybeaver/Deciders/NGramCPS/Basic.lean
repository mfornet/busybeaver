-- TODO: Rewrite Decider in terms of Model rather than Machine
import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability

/-!
Core search algorithm for `NGramCPS`.

This file keeps the executable search and its data structures separate from the
proof support developed in sibling files.
-/

open TM.Table

structure NGramCPSConfig where
  n : ℕ
  bound : ℕ
deriving DecidableEq, Repr

structure NGramCPSHistoryConfig where
  history : ℕ
  left : ℕ
  right : ℕ
  bound : ℕ
deriving DecidableEq, Repr

structure NGramCPSLRUConfig where
  left : ℕ
  right : ℕ
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
deriving DecidableEq, Repr

/-- Result of the bounded finite-window search before it is mapped into `HaltM`. -/
inductive SearchResult (l s : ℕ) where
  | closed (state : SearchState l s)
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
  | closed (state : SearchState l s)
  | haltingEdge
  | timeout
  | restart (remaining : ℕ) (state : SearchState l s)
deriving DecidableEq, Repr

namespace NGramCPS

def insertIfNew [DecidableEq α] (as : Array α) (a : α) : Array α :=
  if a ∈ as then
    as
  else
    as.push a

def insertAllIfNew [DecidableEq α] (base extra : Array α) : Array α :=
  extra.toList.foldl insertIfNew base

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
      some (ngram.getD prefixArr.size fallback)
    else
      none)

/-- Expand a step to the right by reconstructing the unseen symbol on the right. -/
def expandRight (rightNGrams : Array (NGram s)) (cfg : PartialConfig l s) (writeSym : Symbol s)
    (nextState : Label l) : Expansion l s :=
  let newLeft := shiftInNear writeSym cfg.left
  let rightPrefix := cfg.right.drop 1
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
    -- Record the OLD left window `cfg.left` (Coq `xset_ins ls l0`), not the shifted
    -- `newLeft`.  Recording the head-adjacent post-write window over-approximates
    -- the reconstruction pool and makes the abstraction strictly coarser.
    leftNGrams := #[cfg.left]
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
    -- Record the OLD right window `cfg.right` (Coq `xset_ins rs r0`), not `newRight`.
    rightNGrams := #[cfg.right]
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
expansion during the current inner pass.
-/
def addSuccessors (known : Array (PartialConfig l s)) (frontier : List (PartialConfig l s))
    (successors : Array (PartialConfig l s)) :
    Array (PartialConfig l s) × List (PartialConfig l s) :=
  successors.toList.foldl
    (fun (acc : Array (PartialConfig l s) × List (PartialConfig l s)) cfg =>
      let (knownAcc, frontierAcc) := acc
      if cfg ∈ knownAcc  then
        acc
      else
        (knownAcc.push cfg, cfg :: frontierAcc))
    (known, frontier)

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
            .closed state
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

def runSearchOuter (M : Machine l s) : ℕ → ℕ → SearchState l s → SearchResult l s
  | 0, _, _ => .timeout
  | rounds + 1, remaining, state =>
      match runRound M remaining state false with
      | .closed state' => .closed state'
      | .haltingEdge => .haltingEdge
      | .timeout => .timeout
      | .restart remaining' state' => runSearchOuter M rounds remaining' state'

def runSearch (M : Machine l s) (bound : ℕ) (state : SearchState l s) : SearchResult l s :=
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

/-!
## Executable generic NGramCPS

The definitions below are an algorithm-only port of the generic Coq NGramCPS
implementation.  Unlike the proof-oriented definitions above, the tape alphabet
is a parameter, so the same search can run over augmented alphabets such as the
fixed-length update history used by Coq's `NGramCPS_decider_impl1`.
-/

namespace NGramCPS.Generic

structure PartialConfig (l : ℕ) (α : Type _) where
  left : Array α
  head : α
  state : Label l
  right : Array α
deriving DecidableEq, Repr

structure SearchState (l : ℕ) (α : Type _) where
  leftNGrams : Array (Array α)
  rightNGrams : Array (Array α)
  partialConfigs : Array (PartialConfig l α)
  frontier : List (PartialConfig l α)
deriving DecidableEq, Repr

structure Expansion (l : ℕ) (α : Type _) where
  leftNGrams : Array (Array α)
  rightNGrams : Array (Array α)
  successors : Array (PartialConfig l α)
deriving Repr

inductive StepResult (l : ℕ) (α : Type _) where
  | haltingEdge
  | advanced (expansion : Expansion l α)
deriving Repr

inductive RoundResult (l : ℕ) (α : Type _) where
  | closed (state : SearchState l α)
  | haltingEdge
  | timeout
  | restart (remaining : ℕ) (state : SearchState l α)
deriving DecidableEq, Repr

inductive SearchResult (l : ℕ) (α : Type _) where
  | closed (state : SearchState l α)
  | haltingEdge
  | timeout
deriving DecidableEq, Repr

abbrev Transition (l : ℕ) (α : Type _) := Label l → α → Option (α × Turing.Dir × Label l)

def expandRight [Inhabited α] [DecidableEq α] (rightNGrams : Array (Array α))
    (cfg : PartialConfig l α) (writeSym : α) (nextState : Label l) : Expansion l α :=
  let newLeft := NGramCPS.shiftInNear writeSym cfg.left
  let rightPrefix := cfg.right.drop 1
  let newHead := cfg.right.getD 0 default
  let successors :=
    NGramCPS.matchingLastSymbols rightPrefix rightNGrams default |>.map fun sym ↦
      {
        left := newLeft
        head := newHead
        state := nextState
        right := NGramCPS.appendFar rightPrefix sym
      }
  {
    -- Record the OLD left window `cfg.left` (Coq `xset_ins ls l0`), not `newLeft`.
    leftNGrams := #[cfg.left]
    rightNGrams := #[]
    successors
  }

def expandLeft [Inhabited α] [DecidableEq α] (leftNGrams : Array (Array α))
    (cfg : PartialConfig l α) (writeSym : α) (nextState : Label l) : Expansion l α :=
  let newRight := NGramCPS.shiftInNear writeSym cfg.right
  let leftPrefix := cfg.left.drop 1
  let newHead := cfg.left.getD 0 default
  let successors :=
    NGramCPS.matchingLastSymbols leftPrefix leftNGrams default |>.map fun sym ↦
      {
        left := NGramCPS.appendFar leftPrefix sym
        head := newHead
        state := nextState
        right := newRight
      }
  {
    leftNGrams := #[]
    -- Record the OLD right window `cfg.right` (Coq `xset_ins rs r0`), not `newRight`.
    rightNGrams := #[cfg.right]
    successors
  }

def stepPartialConfig [Inhabited α] [DecidableEq α] (tm : Transition l α)
    (leftNGrams rightNGrams : Array (Array α)) (cfg : PartialConfig l α) :
    StepResult l α :=
  match tm cfg.state cfg.head with
  | none => .haltingEdge
  | some (writeSym, .right, nextState) => .advanced (expandRight rightNGrams cfg writeSym nextState)
  | some (writeSym, .left, nextState) => .advanced (expandLeft leftNGrams cfg writeSym nextState)

def addSuccessors [DecidableEq α] (known : Array (PartialConfig l α))
    (frontier : List (PartialConfig l α)) (successors : Array (PartialConfig l α)) :
    Array (PartialConfig l α) × List (PartialConfig l α) × Bool :=
  successors.toList.foldl
    (fun (acc : Array (PartialConfig l α) × List (PartialConfig l α) × Bool) cfg =>
      let (knownAcc, frontierAcc, _changed) := acc
      if cfg ∈ knownAcc then
        acc
      else
        (knownAcc.push cfg, cfg :: frontierAcc, true))
    (known, frontier, false)

def runRound [Inhabited α] [DecidableEq α] (tm : Transition l α) :
    ℕ → SearchState l α → Bool → RoundResult l α
  | bound, state, changed =>
      match state.frontier with
      | [] =>
          if changed then
            .restart bound { state with frontier := state.partialConfigs.toList }
          else
            .closed state
      | cfg :: rest =>
          match bound with
          | 0 => .timeout
          | bound' + 1 =>
              match stepPartialConfig tm state.leftNGrams state.rightNGrams cfg with
              | .haltingEdge => .haltingEdge
              | .advanced expansion =>
                  let nextLeft := NGramCPS.insertAllIfNew state.leftNGrams expansion.leftNGrams
                  let nextRight := NGramCPS.insertAllIfNew state.rightNGrams expansion.rightNGrams
                  let (nextConfigs, nextFrontier, configsChanged) :=
                    addSuccessors state.partialConfigs rest expansion.successors
                  let changed' :=
                    changed ||
                    configsChanged ||
                    nextLeft.size ≠ state.leftNGrams.size ||
                    nextRight.size ≠ state.rightNGrams.size
                  runRound tm bound' {
                    leftNGrams := nextLeft
                    rightNGrams := nextRight
                    partialConfigs := nextConfigs
                    frontier := nextFrontier
                  } changed'

def runSearchOuter [Inhabited α] [DecidableEq α] (tm : Transition l α) :
    ℕ → ℕ → SearchState l α → SearchResult l α
  | 0, _, _ => .timeout
  | rounds + 1, remaining, state =>
      match runRound tm remaining state false with
      | .closed state' => .closed state'
      | .haltingEdge => .haltingEdge
      | .timeout => .timeout
      | .restart remaining' state' => runSearchOuter tm rounds remaining' state'

def runSearch [Inhabited α] [DecidableEq α] (tm : Transition l α) (bound : ℕ)
    (state : SearchState l α) : SearchResult l α :=
  runSearchOuter tm bound bound state

def initialState [Inhabited α] (left right : ℕ) : SearchState l α :=
  let blankLeft := Array.replicate left default
  let blankRight := Array.replicate right default
  let firstConfig : PartialConfig l α := {
    left := blankLeft
    head := default
    state := default
    right := blankRight
  }
  {
    leftNGrams := #[blankLeft]
    rightNGrams := #[blankRight]
    partialConfigs := #[firstConfig]
    frontier := [firstConfig]
  }

def standardTransition (M : Machine l s) : Transition l (Symbol s) :=
  fun state sym =>
    match M.get state sym with
    | .halt => none
    | .next writeSym dir nextState => some (writeSym, dir, nextState)

abbrev HistorySymbol (l s : ℕ) := Symbol s × List (Label l × Symbol s)

instance : Inhabited (HistorySymbol l s) := ⟨(default, [])⟩

def historyTransition (history : ℕ) (M : Machine l s) : Transition l (HistorySymbol l s) :=
  fun state sym =>
    match M.get state sym.fst with
    | .halt => none
    | .next writeSym dir nextState =>
        some ((writeSym, ((state, sym.fst) :: sym.snd).take history), dir, nextState)

def lruTransition (M : Machine l s) : Transition l (HistorySymbol l s) :=
  fun state sym =>
    match M.get state sym.fst with
    | .halt => none
    | .next writeSym dir nextState =>
        some ((writeSym, (state, sym.fst) :: sym.snd.filter (· ≠ (state, sym.fst))), dir, nextState)

def runStandard (left right bound : ℕ) (M : Machine l s) : SearchResult l (Symbol s) :=
  if left = 0 || right = 0 then
    .timeout
  else
    runSearch (standardTransition M) bound (initialState (l := l) left right)

def runHistory (cfg : NGramCPSHistoryConfig) (M : Machine l s) :
    SearchResult l (HistorySymbol l s) :=
  if cfg.left = 0 || cfg.right = 0 then
    .timeout
  else
    runSearch (historyTransition cfg.history M) cfg.bound
      (initialState (l := l) cfg.left cfg.right)

def runLRU (cfg : NGramCPSLRUConfig) (M : Machine l s) :
    SearchResult l (HistorySymbol l s) :=
  if cfg.left = 0 || cfg.right = 0 then
    .timeout
  else
    runSearch (lruTransition M) cfg.bound
      (initialState (l := l) cfg.left cfg.right)

def decidedClosed : SearchResult l α → Bool
  | .closed _ => true
  | .haltingEdge => false
  | .timeout => false

end NGramCPS.Generic
