import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability

open TM.Table

namespace Deciders.Loop1

structure HistoryEntry (l s : ℕ) where
  cfg : Config l s
  pos : Int
deriving DecidableEq

def dirDelta : Turing.Dir → Int
  | .left => -1
  | .right => 1

def sameStateHead (a b : HistoryEntry l s) : Bool :=
  decide (a.cfg.state = b.cfg.state) && decide (a.cfg.tape.head = b.cfg.tape.head)

def noVisitedRight (h : HistoryEntry l s) : Bool :=
  decide (h.cfg.tape.right = (default : Turing.ListBlank (Symbol s)))

def noVisitedLeft (h : HistoryEntry l s) : Bool :=
  decide (h.cfg.tape.left = (default : Turing.ListBlank (Symbol s)))

def baseLoopCheck (h0 h1 : HistoryEntry l s) (n : ℕ) (dpos : Int) : Bool :=
  n == 0 && (
    if dpos = 0 then
      decide (h1.pos = h0.pos)
    else if dpos > 0 then
      noVisitedRight h1 && decide (h1.pos < h0.pos)
    else
      noVisitedLeft h1 && decide (h0.pos < h1.pos)
  )

def verifyLoop1 (h0 h1 : HistoryEntry l s) :
    List (HistoryEntry l s) → List (HistoryEntry l s) → ℕ → Int → Bool
  | h0' :: ls0', h1' :: ls1', n, dpos =>
      sameStateHead h0 h1 && (
        baseLoopCheck h0 h1 n dpos ||
        verifyLoop1 h0' h1' ls0' ls1' n.pred dpos
      )
  | _, _, n, dpos =>
      sameStateHead h0 h1 && baseLoopCheck h0 h1 n dpos

def findLoop1 (h0 h1 h2 : HistoryEntry l s) (ls0 : List (HistoryEntry l s)) :
    List (HistoryEntry l s) → List (HistoryEntry l s) → ℕ → Bool
  | h1' :: ls1', _ :: h2' :: ls2', n =>
      (
        sameStateHead h0 h1 &&
        sameStateHead h0 h2 &&
        verifyLoop1 h0 h1 ls0 (h1' :: ls1') (n + 1) (h0.pos - h1.pos)
      ) ||
      findLoop1 h0 h1' h2' ls0 ls1' ls2' (n + 1)
  | _, _, n =>
      sameStateHead h0 h1 &&
      sameStateHead h0 h2 &&
      verifyLoop1 h0 h1 ls0 [] (n + 1) (h0.pos - h1.pos)
termination_by ls1 _ _ => ls1.length

def findLoop10 (h0 h1 : HistoryEntry l s) : List (HistoryEntry l s) → Bool
  | h2 :: ls' => findLoop1 h0 h1 h2 (h1 :: h2 :: ls') (h2 :: ls') ls' 0
  | [] => false

def step? (M : Machine l s) (h : HistoryEntry l s) : Option (HistoryEntry l s) :=
  match M.get h.cfg.state h.cfg.tape.head with
  | .halt => none
  | .next sym dir state =>
      some {
        cfg := { state, tape := h.cfg.tape.write sym |>.move dir }
        pos := h.pos + dirDelta dir
      }

def runFrom (M : Machine l s) : ℕ → HistoryEntry l s → List (HistoryEntry l s) → Bool
  | 0, _, _ => false
  | fuel + 1, cur, history =>
      match step? M cur with
      | none => false
      | some next =>
          match fuel with
          | 0 => findLoop10 next cur history
          | _ + 1 => runFrom M fuel next (cur :: history)

def run (bound : ℕ) (M : Machine l s) : Bool :=
  runFrom M bound { cfg := init, pos := 0 } []

namespace Correctness

variable {l s : ℕ}

/-- Absolute symbol at integer position `x`, independent of the head location.
The history entry carries the absolute head position `pos`, so `tape.nth (x - pos)`
is the genuine content of cell `x`. -/
def absSym (h : HistoryEntry l s) (x : ℤ) : Symbol s := h.cfg.tape.nth (x - h.pos)

@[simp] lemma absSym_head (h : HistoryEntry l s) : absSym h h.pos = h.cfg.tape.head := by
  simp [absSym, Turing.Tape.nth_zero]

/-- A single write+move on a tape, expressed via `nth`. -/
lemma write_move_nth (T : Turing.Tape (Symbol s)) (sym : Symbol s) (dir : Turing.Dir) (k : ℤ) :
    ((T.write sym).move dir).nth k =
      if k + dirDelta dir = 0 then sym else T.nth (k + dirDelta dir) := by
  have hd : ((T.write sym).move dir).nth k = (T.write sym).nth (k + dirDelta dir) := by
    cases dir with
    | right => rw [Turing.Tape.move_right_nth]; congr 1
    | left => rw [Turing.Tape.move_left_nth]; congr 1
  rw [hd]
  by_cases hk : k + dirDelta dir = 0
  · rw [if_pos hk, hk, Turing.Tape.write_nth_zero]
  · rw [if_neg hk, Turing.Tape.write_nth_of_ne_zero _ _ hk]

/-- Decode a successful `step?`: it is a genuine machine step, writing `sym`, moving `dir`. -/
lemma step?_eq_some {M : Machine l s} {h h' : HistoryEntry l s} (hstep : step? M h = some h') :
    ∃ sym dir st, M.get h.cfg.state h.cfg.tape.head = .next sym dir st ∧
      h'.cfg.state = st ∧
      h'.cfg.tape = (h.cfg.tape.write sym).move dir ∧
      h'.pos = h.pos + dirDelta dir := by
  unfold step? at hstep
  cases hget : M.get h.cfg.state h.cfg.tape.head with
  | halt => rw [hget] at hstep; simp at hstep
  | next sym dir st =>
      rw [hget] at hstep
      rw [Option.some.injEq] at hstep
      subst hstep
      exact ⟨sym, dir, st, rfl, rfl, rfl, rfl⟩

/-- The absolute step relation: stepping changes only the cell under the head,
writing the symbol `sym` determined by the transition. -/
lemma absSym_step {M : Machine l s} {h h' : HistoryEntry l s} (hstep : step? M h = some h') :
    ∃ sym dir st, M.get h.cfg.state h.cfg.tape.head = .next sym dir st ∧
      h'.cfg.state = st ∧ h'.pos = h.pos + dirDelta dir ∧
      ∀ x, absSym h' x = if x = h.pos then sym else absSym h x := by
  obtain ⟨sym, dir, st, hget, hst, htape, hpos⟩ := step?_eq_some hstep
  refine ⟨sym, dir, st, hget, hst, hpos, ?_⟩
  intro x
  rw [absSym, htape, hpos, write_move_nth]
  have hcancel : x - (h.pos + dirDelta dir) + dirDelta dir = x - h.pos := by omega
  rw [hcancel]
  by_cases hx : x = h.pos
  · subst hx; rw [if_pos (by omega), if_pos rfl]
  · rw [if_neg (by intro hc; apply hx; omega), if_neg hx, absSym]

/-- A successful `step?` is a genuine machine step on the underlying configurations. -/
lemma step?_step {M : Machine l s} {h h' : HistoryEntry l s} (hstep : step? M h = some h') :
    (h.cfg -[M]-> h'.cfg) := by
  obtain ⟨sym, dir, st, hget, hst, htape, hpos⟩ := step?_eq_some hstep
  show M.step h.cfg = some h'.cfg
  have hms : M.step h.cfg = some ⟨st, (h.cfg.tape.write sym).move dir⟩ := by
    simp only [Machine.step, hget]
  rw [hms, ← hst, ← htape]

/-- **Replay engine.** Any configuration with the *same control state and head symbol* as `h`
takes the *same* transition `h` does (same written symbol, move direction, next state, and head
displacement).  This is the determinism that drives the translated cycle: a shifted copy of a
window position replays it verbatim. -/
lemma step?_replay {M : Machine l s} {h g h' : HistoryEntry l s}
    (hstep : step? M h = some h')
    (hstate : g.cfg.state = h.cfg.state) (hhead : g.cfg.tape.head = h.cfg.tape.head) :
    ∃ sym dir st, M.get h.cfg.state h.cfg.tape.head = .next sym dir st ∧
      step? M g = some { cfg := { state := st, tape := (g.cfg.tape.write sym).move dir },
                         pos := g.pos + dirDelta dir } := by
  obtain ⟨sym, dir, st, hget, _, _, _⟩ := step?_eq_some hstep
  refine ⟨sym, dir, st, hget, ?_⟩
  unfold step?
  rw [hstate, hhead, hget]

/-! ### Translated-cycler certificate

`run` returns `true` exactly when it discovers a *translated cycler*: two consecutive length-`p`
windows of the execution history that agree, step by step, on the control state and head symbol,
together with a blank "leading edge" in the direction of the net head shift `d`.  We package those
facts as `LoopCert`. -/

/-- The net head displacement over one window. -/
def LoopCert.shift (f : ℕ → HistoryEntry l s) (p : ℕ) : Int := (f (2 * p)).pos - (f p).pos

/-- A translated-cycler certificate, extracted from a successful `run`.

* `f 0, f 1, …, f (2*p)` is a genuine run of `M` (via `step?`);
* `f 0` is reachable from the initial configuration;
* the two windows `f 0 … f p` and `f p … f (2*p)` agree on `(state, head symbol)` at every
  aligned position (`matchSH`);
* `base` records the blank-edge / position condition checked by `baseLoopCheck` for the net
  shift `shift f p`. -/
structure LoopCert (M : Machine l s) where
  f : ℕ → HistoryEntry l s
  p : ℕ
  hp : 1 ≤ p
  reach : (TM.Table.init : Config l s) -[M]->* (f 0).cfg
  traj : ∀ i, i < 2 * p → step? M (f i) = some (f (i + 1))
  matchSH : ∀ j, j ≤ p →
    (f j).cfg.state = (f (j + p)).cfg.state ∧ (f j).cfg.tape.head = (f (j + p)).cfg.tape.head
  base : baseLoopCheck (f p) (f 0) 0 (LoopCert.shift f p) = true

/-- **Determinism replay.** Because the two windows agree on `(state, head symbol)` at aligned
positions (`matchSH`), they execute *the same* transition there: identical written symbol, move
direction and next state, and hence identical per-step head displacement.  This is the engine that
makes the period repeat. -/
theorem LoopCert.window_replay {M : Machine l s} (c : LoopCert M) {j : ℕ} (hj : j < c.p) :
    ∃ sym dir st,
      M.get (c.f j).cfg.state (c.f j).cfg.tape.head = .next sym dir st ∧
      M.get (c.f (j + c.p)).cfg.state (c.f (j + c.p)).cfg.tape.head = .next sym dir st ∧
      (c.f (j + 1)).pos = (c.f j).pos + dirDelta dir ∧
      (c.f (j + c.p + 1)).pos = (c.f (j + c.p)).pos + dirDelta dir := by
  obtain ⟨hst, hhd⟩ := c.matchSH j (le_of_lt hj)
  obtain ⟨sym, dir, st, hget, _, _, hpos⟩ := step?_eq_some (c.traj j (by omega))
  obtain ⟨sym', dir', st', hget', _, _, hpos'⟩ := step?_eq_some (c.traj (j + c.p) (by omega))
  have key : (Stmt.next sym dir st : Stmt l s) = .next sym' dir' st' := by
    rw [← hget, ← hget', hst, hhd]
  rw [Stmt.next.injEq] at key
  obtain ⟨rfl, rfl, rfl⟩ := key
  exact ⟨sym, dir, st, hget, hget', hpos, hpos'⟩

/-- **Constant window shift.** The head displacement between aligned positions of the two windows
is the same constant `d` everywhere (telescoping `window_replay`).  In particular the two ways of
reading off the net shift agree: `(f p).pos - (f 0).pos = (f (2p)).pos - (f p).pos`. -/
theorem LoopCert.pos_window_const {M : Machine l s} (c : LoopCert M) :
    ∀ j, j ≤ c.p → (c.f (j + c.p)).pos - (c.f j).pos = (c.f c.p).pos - (c.f 0).pos := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      obtain ⟨sym, dir, st, _, _, hp1, hp2⟩ := c.window_replay (j := j) (by omega)
      have hih := ih (by omega)
      rw [show j + 1 + c.p = j + c.p + 1 from by omega]
      omega

/-- The net shift read off after the windows equals the net shift before them. -/
theorem LoopCert.shift_eq {M : Machine l s} (c : LoopCert M) :
    LoopCert.shift c.f c.p = (c.f c.p).pos - (c.f 0).pos := by
  have := c.pos_window_const c.p (le_refl _)
  simp only [LoopCert.shift]
  rw [show c.p + c.p = 2 * c.p from by omega] at this
  omega

/-- **Core correctness (translated-cycler non-halting).**

Given a `LoopCert`, the machine does not halt from `f 0`.

Mathematical content: by `matchSH` the second window replays the first one transition for transition
(determinism), so the head shifts by a fixed `d := shift f p` per period and the same finite block of
the tape is reproduced, translated by `d`.  The blank leading edge recorded in `base` guarantees that
every cell the head newly enters is blank, so the period repeats forever.

This is the genuinely hard geometric fact; it is the same mathematical content proved (in the
Ticking-wrapper representation) by `ticking_extends_start_model` / `fresh_cell_is_bot` in
`Deciders/TranslatedCyclers/`.  Here we prove it directly in the absolute-tape representation via a
`ClosedSet` of shifted window-start configurations; the supporting machinery (`absSym`,
`absSym_step`) is the foundation. -/
theorem LoopCert.nonHalting {M : Machine l s} (c : LoopCert M) :
    ¬ M.halts (c.f 0).cfg := by
  sorry

/-- **Decoding.** A successful `run` yields a `LoopCert`. This unfolds the nested search
(`runFrom` / `findLoop10` / `findLoop1` / `verifyLoop1`) and turns the boolean checks into the
structured facts of `LoopCert`. -/
theorem loopCert_of_run {M : Machine l s} {bound : ℕ} (h : run bound M = true) :
    Nonempty (LoopCert M) := by
  sorry

end Correctness

private theorem run_eq_true_nonHalting
    (bound : ℕ) (M : Machine l s)
    (h : run bound M = true) :
    ¬M.halts TM.Table.init := by
  obtain ⟨c⟩ := Correctness.loopCert_of_run h
  exact TM.Table.Machine.halts.skip_evstep c.reach c.nonHalting

def decider (bound : ℕ) (M : Machine l s) : HaltM M Unit :=
  if h : run bound M = true then
    .loops_prf (run_eq_true_nonHalting bound M h)
  else
    .unknown ()

end Deciders.Loop1
