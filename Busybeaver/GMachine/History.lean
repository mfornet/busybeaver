import Busybeaver.Basic

namespace GMachine

variable {Machine State Symbol : Type _} {k : ℕ}

/--
A tape symbol that remembers the current symbol together with the most recent
state/symbol pairs seen at that cell, stored newest first.
-/
structure HistorySymbol (State Symbol : Type _) (k : ℕ) where
  current : Symbol
  -- TODO(perf): Consider using an Array rather than a function.
  recent : Fin k → Option (Symbol × State)
deriving DecidableEq

namespace HistorySymbol

def ofSymbol (sym : Symbol) : HistorySymbol State Symbol k where
  current := sym
  recent := fun _ => none

def history (cell : HistorySymbol State Symbol k) : List (Symbol × State) :=
  (List.ofFn cell.recent).filterMap id

private def pushRecent (entry : Symbol × State) (recent : Fin k → Option (Symbol × State)) :
    Fin k → Option (Symbol × State)
  | ⟨0, _⟩ => some entry
  | ⟨n + 1, hn⟩ => recent ⟨n, Nat.lt_of_succ_lt hn⟩

/--
Record one visit to a cell by pushing the current `(symbol, state)` pair into the
bounded history and updating the current symbol to the newly written symbol.
-/
def record (cell : HistorySymbol State Symbol k) (state : State) (next : Symbol) :
    HistorySymbol State Symbol k where
  current := next
  recent := pushRecent (cell.current, state) cell.recent

def forget (cell : HistorySymbol State Symbol k) : Symbol := cell.current

@[simp]
lemma ofSymbol_current (sym : Symbol) :
    (ofSymbol (State := State) (k := k) sym).current = sym := rfl

@[simp]
lemma ofSymbol_history (sym : Symbol) :
    (ofSymbol (State := State) (k := k) sym).history = [] := by
  simp [ofSymbol, history]

@[simp]
lemma record_current (cell : HistorySymbol State Symbol k) (state : State) (next : Symbol) :
    (cell.record state next).current = next := rfl

@[simp]
lemma forget_ofSymbol (sym : Symbol) :
    (ofSymbol (State := State) (k := k) sym).forget = sym := rfl

@[simp]
lemma forget_record (cell : HistorySymbol State Symbol k) (state : State) (next : Symbol) :
    (cell.record state next).forget = next := rfl

end HistorySymbol

instance [BlankSymbol Symbol] : BlankSymbol (HistorySymbol State Symbol k) :=
  ⟨HistorySymbol.ofSymbol blank⟩

instance [Fintype State] [Fintype Symbol] : Fintype (HistorySymbol State Symbol k) := by
  classical
  let e : HistorySymbol State Symbol k ≃ Symbol × (Fin k → Option (Symbol × State)) := {
    toFun := fun cell => (cell.current, cell.recent)
    invFun := fun cell => ⟨cell.1, cell.2⟩
    left_inv := by
      intro cell
      cases cell
      rfl
    right_inv := by
      intro cell
      cases cell
      rfl
  }
  exact Fintype.ofEquiv (Symbol × (Fin k → Option (Symbol × State))) e.symm

/-- Wrap a machine so that each tape cell remembers the last `k` visits to it. -/
structure WithHistory (Machine State Symbol : Type _) (k : ℕ) where
  base : Machine

def withHistory (M : Machine) : WithHistory Machine State Symbol k := ⟨M⟩

@[simp]
lemma withHistory_base (M : Machine) :
    (withHistory (State := State) (Symbol := Symbol) (k := k) M).base = M := rfl

instance [GMachine Machine State Symbol] :
    GMachine (WithHistory Machine State Symbol k) State (HistorySymbol State Symbol k) where
  trans M state cell :=
    match GMachine.trans M.base state cell.current with
    | .halt => .halt
    | .next write dir nextState => .next (cell.record state write) dir nextState

end GMachine
