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

/-! ### Shift-agreement invariant

The engine of the non-halting proof. `AgreeShift d Reg b a` says config `b` is config `a`
translated to the right by `d`: same control state, head displaced by `d`, and the absolute tape
content of `b` at `x + d` is a verbatim copy of `a`'s content at `x` for every `x` in the region
`Reg`.  The key facts are that the heads then agree (`head_eq`) and that the relation is preserved
by one machine step on both configs (`step`).  Iterating `step` turns one window of replay into an
infinite periodic run.  The region `Reg` lets the same engine cover right-translation (`Reg = (m ≤
·)`), left-translation (`Reg = (· ≤ M)`) and pure cycles (`Reg = True`). -/

/-- `b` is `a` translated right by `d`, with the tapes agreeing (shifted) on the region `Reg`. -/
def AgreeShift (d : ℤ) (Reg : ℤ → Prop) (b a : HistoryEntry l s) : Prop :=
  b.cfg.state = a.cfg.state ∧ b.pos = a.pos + d ∧
    ∀ x, Reg x → absSym b (x + d) = absSym a x

/-- Under `AgreeShift`, the two heads read the same symbol (when `a`'s head is in the region). -/
lemma AgreeShift.head_eq {d : ℤ} {Reg : ℤ → Prop} {b a : HistoryEntry l s}
    (hag : AgreeShift d Reg b a) (hRa : Reg a.pos) :
    b.cfg.tape.head = a.cfg.tape.head := by
  obtain ⟨_, hpos, hag3⟩ := hag
  rw [← absSym_head b, ← absSym_head a, hpos]
  exact hag3 a.pos hRa

/-- **One-step preservation.** If `b` is `a` shifted by `d` and `a` steps, then `b` takes the same
transition (by determinism) and the resulting configs are again shifted by `d`. -/
lemma AgreeShift.step {M : Machine l s} {d : ℤ} {Reg : ℤ → Prop} {a a' b : HistoryEntry l s}
    (hag : AgreeShift d Reg b a) (hRa : Reg a.pos) (ha : step? M a = some a') :
    ∃ b', step? M b = some b' ∧ AgreeShift d Reg b' a' := by
  obtain ⟨hstate, hpos, hag3⟩ := hag
  have hhead : b.cfg.tape.head = a.cfg.tape.head := AgreeShift.head_eq ⟨hstate, hpos, hag3⟩ hRa
  obtain ⟨symA, dirA, stA, hgetA, hstA, hposA, habsA⟩ := absSym_step ha
  obtain ⟨symR, dirR, stR, _, hbstep⟩ := step?_replay ha hstate hhead
  refine ⟨_, hbstep, ?_⟩
  obtain ⟨symB, dirB, stB, hgetB, hstB, hposB, habsB⟩ := absSym_step hbstep
  have hgetab : M.get b.cfg.state b.cfg.tape.head = M.get a.cfg.state a.cfg.tape.head := by
    rw [hstate, hhead]
  rw [hgetab, hgetA] at hgetB
  simp only [Stmt.next.injEq] at hgetB
  obtain ⟨hsym, hdir, hst⟩ := hgetB
  refine ⟨by rw [hstB, hstA, hst], by rw [hposB, hposA, hpos, hdir]; omega, ?_⟩
  intro x hx
  rw [habsB, habsA]
  by_cases hxa : x = a.pos
  · have hb : x + d = b.pos := by rw [hpos, hxa]
    rw [if_pos hb, if_pos hxa]; exact hsym.symm
  · have hne : x + d ≠ b.pos := by rw [hpos]; intro h; exact hxa (by omega)
    rw [if_neg hne, if_neg hxa]
    exact hag3 x hx

/-- Cells right of the head are blank when the right side of the tape is the default `ListBlank`. -/
lemma absSym_of_right_blank {h : HistoryEntry l s} (hR : h.cfg.tape.right = default) :
    ∀ x, h.pos < x → absSym h x = (default : Symbol s) := by
  intro x hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x - h.pos = ((n + 1 : ℕ) : ℤ) := ⟨(x - h.pos - 1).toNat, by omega⟩
  have hstep : absSym h x = h.cfg.tape.right.nth n := by rw [absSym, hn]; rfl
  rw [hstep, hR, Turing.ListBlank.default_nth]

/-- Cells left of the head are blank when the left side of the tape is the default `ListBlank`. -/
lemma absSym_of_left_blank {h : HistoryEntry l s} (hL : h.cfg.tape.left = default) :
    ∀ x, x < h.pos → absSym h x = (default : Symbol s) := by
  intro x hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x - h.pos = -((n + 1 : ℕ) : ℤ) := ⟨(h.pos - x - 1).toNat, by omega⟩
  have hstep : absSym h x = h.cfg.tape.left.nth n := by rw [absSym, hn]; rfl
  rw [hstep, hL, Turing.ListBlank.default_nth]

/-- A cell never visited by a `step?`-run keeps its content. -/
lemma absSym_const_of_unvisited {M : Machine l s} {e : ℕ → HistoryEntry l s} {x : ℤ} {a : ℕ} :
    ∀ k, (∀ i, i < k → step? M (e (a + i)) = some (e (a + i + 1))) →
      (∀ i, i < k → (e (a + i)).pos ≠ x) →
      absSym (e (a + k)) x = absSym (e a) x := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
      intro hrun hvis
      obtain ⟨sym, dir, st, _, _, _, habs⟩ := absSym_step (hrun k (by omega))
      have hne : (e (a + k)).pos ≠ x := hvis k (by omega)
      have hkeep : absSym (e (a + k + 1)) x = absSym (e (a + k)) x := by
        rw [habs x, if_neg (fun h => hne h.symm)]
      rw [show a + (k + 1) = a + k + 1 from by omega, hkeep]
      exact ih (fun i hi => hrun i (by omega)) (fun i hi => hvis i (by omega))

/-! ### Discrete intermediate-value theorem for ±1 paths

A path that steps by `±1` and brackets a value `z` (some index is `≤ z`, some is `≥ z`) must hit
`z`.  Used to show that the head's visited cells form a contiguous interval, so any unvisited cell
in range lies strictly beyond every visited cell on one side. -/

private lemma int_path_crosses {q : ℕ → ℤ} :
    ∀ n, (∀ i, i < n → q (i + 1) = q i + 1 ∨ q (i + 1) = q i - 1) →
      ∀ z : ℤ, q 0 ≤ z → z ≤ q n → ∃ k, k ≤ n ∧ q k = z := by
  intro n
  induction n with
  | zero => intro _ z h0 hn; exact ⟨0, le_refl _, le_antisymm h0 hn⟩
  | succ n ih =>
      intro hstep z h0 hn
      by_cases hzn : z ≤ q n
      · obtain ⟨k, hk, hqk⟩ := ih (fun i hi => hstep i (by omega)) z h0 hzn
        exact ⟨k, by omega, hqk⟩
      · rcases hstep n (by omega) with h | h
        · exact ⟨n + 1, le_refl _, by omega⟩
        · exact absurd hn (by omega)

private lemma int_path_crosses_down {q : ℕ → ℤ} :
    ∀ n, (∀ i, i < n → q (i + 1) = q i + 1 ∨ q (i + 1) = q i - 1) →
      ∀ z : ℤ, z ≤ q 0 → q n ≤ z → ∃ k, k ≤ n ∧ q k = z := by
  intro n
  induction n with
  | zero => intro _ z h0 hn; exact ⟨0, le_refl _, le_antisymm hn h0⟩
  | succ n ih =>
      intro hstep z h0 hn
      by_cases hzn : q n ≤ z
      · obtain ⟨k, hk, hqk⟩ := ih (fun i hi => hstep i (by omega)) z h0 hzn
        exact ⟨k, by omega, hqk⟩
      · rcases hstep n (by omega) with h | h
        · exact absurd hn (by omega)
        · exact ⟨n + 1, le_refl _, by omega⟩

private lemma int_path_bracket {q : ℕ → ℤ} {K : ℕ}
    (hstep : ∀ i, i < K → q (i + 1) = q i + 1 ∨ q (i + 1) = q i - 1) :
    ∀ a b, a ≤ K → b ≤ K → ∀ z : ℤ, q a ≤ z → z ≤ q b → ∃ k, k ≤ K ∧ q k = z := by
  intro a b ha hb z hza hzb
  rcases le_total a b with hab | hab
  · -- forward sub-path starting at `a`
    obtain ⟨k, hk, hqk⟩ :=
      int_path_crosses (q := fun i => q (a + i)) (b - a)
        (fun i hi => hstep (a + i) (by omega)) z (by simpa using hza)
        (by rw [show a + (b - a) = b from by omega]; exact hzb)
    exact ⟨a + k, by omega, hqk⟩
  · -- descending sub-path starting at `b`
    obtain ⟨k, hk, hqk⟩ :=
      int_path_crosses_down (q := fun i => q (b + i)) (a - b)
        (fun i hi => hstep (b + i) (by omega)) z (by simpa using hzb)
        (by rw [show b + (a - b) = a from by omega]; exact hza)
    exact ⟨b + k, by omega, hqk⟩

/-! ### Two-window agreement (last-write argument)

`window_pair_inv` compares the two recorded length-`p` windows `f 0 … f p` and `f p … f (2p)`.
The two windows take identical transitions (`hwsym`: equal written symbols at positions shifted by
`d`), so at every cell *visited* in the first window the second window (shifted by `d`) reproduces
the same content; *unvisited* cells stay at their starting value in both windows.  This is the
clean (no last-write bookkeeping) form: at step `k`, visited and unvisited cells are tracked
separately. -/

private lemma window_pair_inv {M : Machine l s} {f : ℕ → HistoryEntry l s} {p : ℕ} {d : ℤ}
    (hrun1 : ∀ i, i < p → step? M (f i) = some (f (i + 1)))
    (hrun2 : ∀ i, i < p → step? M (f (p + i)) = some (f (p + i + 1)))
    (hposd : ∀ i, i < p → (f (p + i)).pos = (f i).pos + d)
    (hwsym : ∀ i, i < p →
        absSym (f (p + i + 1)) ((f (p + i)).pos) = absSym (f (i + 1)) ((f i).pos)) :
    ∀ k, k ≤ p → ∀ x : ℤ,
      ((∃ i, i < k ∧ (f i).pos = x) → absSym (f (p + k)) (x + d) = absSym (f k) x) ∧
      ((∀ i, i < k → (f i).pos ≠ x) →
        absSym (f (p + k)) (x + d) = absSym (f p) (x + d) ∧ absSym (f k) x = absSym (f 0) x) := by
  intro k
  induction k with
  | zero =>
      intro _ x
      refine ⟨fun h => ?_, fun _ => ⟨rfl, rfl⟩⟩
      obtain ⟨i, hi, _⟩ := h; omega
  | succ k ih =>
      intro hk x
      have hkp : k < p := by omega
      rw [show p + (k + 1) = p + k + 1 from by omega]
      obtain ⟨s1, _, _, _, _, _, ha1⟩ := absSym_step (hrun1 k hkp)
      obtain ⟨s2, _, _, _, _, _, ha2⟩ := absSym_step (hrun2 k hkp)
      have hpk : (f (p + k)).pos = (f k).pos + d := hposd k hkp
      have hs : s1 = s2 := by
        have e1 : absSym (f (k + 1)) ((f k).pos) = s1 := by rw [ha1]; simp
        have e2 : absSym (f (p + k + 1)) ((f (p + k)).pos) = s2 := by rw [ha2]; simp
        have hw := hwsym k hkp
        rw [e2, e1] at hw; exact hw.symm
      have ihk := ih (by omega)
      constructor
      · intro hex
        rw [ha2 (x + d), ha1 x]
        by_cases hxk : x = (f k).pos
        · rw [if_pos (by rw [hpk, hxk]), if_pos hxk, hs]
        · have hxd : (x + d) ≠ (f (p + k)).pos := by omega
          rw [if_neg hxd, if_neg hxk]
          have hvis : ∃ j, j < k ∧ (f j).pos = x := by
            obtain ⟨i, hi, hix⟩ := hex
            have hik : i < k := by
              rcases Nat.lt_or_ge i k with h | h
              · exact h
              · have hik' : i = k := by omega
                rw [hik'] at hix; exact absurd hix.symm hxk
            exact ⟨i, hik, hix⟩
          exact (ihk x).1 hvis
      · intro hun
        have hxk : (f k).pos ≠ x := hun k (by omega)
        have hunk : ∀ i, i < k → (f i).pos ≠ x := fun i hi => hun i (by omega)
        obtain ⟨ihu1, ihu2⟩ := (ihk x).2 hunk
        rw [ha2 (x + d), ha1 x]
        have hxd : (x + d) ≠ (f (p + k)).pos := by omega
        rw [if_neg hxd, if_neg (fun h => hxk h.symm)]
        exact ⟨ihu1, ihu2⟩

/-! ### The infinite periodic extension

`gExt M a` runs `M` forever from `a` via `step?` (stalling on `none`).  The construction lemma
`loopCert_nonHalting_aux` shows that, once the second window is a `d`-shift of the first
(`hbase`) and the shift region is preserved (`hRegClosed`, `hregf2`), every `step?` succeeds, so
the run is genuinely infinite and the machine never halts. -/

private def gExt (M : Machine l s) (a : HistoryEntry l s) : ℕ → HistoryEntry l s
  | 0 => a
  | n + 1 => (step? M (gExt M a n)).getD (gExt M a n)

/-- **The construction.** Given the recorded double window `f 0 … f (2p)`, a region `Reg` closed
under `+d` containing all recorded head positions, and the base shift `AgreeShift d Reg (f 2p)
(f p)`, the extension never halts: each window replays the previous one shifted by `d`. -/
private lemma loopCert_nonHalting_aux {M : Machine l s} {f : ℕ → HistoryEntry l s} {p : ℕ} {d : ℤ}
    {Reg : ℤ → Prop}
    (hp : 1 ≤ p)
    (hrun : ∀ i, i < 2 * p → step? M (f i) = some (f (i + 1)))
    (hRegClosed : ∀ x, Reg x → Reg (x + d))
    (hregf2 : ∀ i, i ≤ 2 * p → Reg (f i).pos)
    (hbase : AgreeShift d Reg (f (2 * p)) (f p)) :
    ¬ M.halts (f 0).cfg := by
  set g := gExt M (f 0) with hg
  have g_zero : g 0 = f 0 := rfl
  have g_succ : ∀ n, g (n + 1) = (step? M (g n)).getD (g n) := fun n => rfl
  -- The extension agrees with the recorded run on `[0, 2p]`.
  have gf : ∀ n, n ≤ 2 * p → g n = f n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
        intro hn
        rw [g_succ, ih (by omega), hrun n (by omega), Option.getD_some]
  -- Strong-induction core: the step always succeeds, positions stay in `Reg`, and each window is a
  -- `d`-shift of the previous one.
  have key : ∀ n, (step? M (g n) = some (g (n + 1))) ∧ Reg (g n).pos ∧
      (2 * p ≤ n → AgreeShift d Reg (g n) (g (n - p))) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      have hAS : 2 * p ≤ n → AgreeShift d Reg (g n) (g (n - p)) := by
        intro hn
        rcases Nat.lt_or_ge (2 * p) n with hlt | _
        · -- `n > 2p`: step the previous window relation forward.
          have hR1 := (IH (n - 1) (by omega)).2.2 (by omega)
          have hReg1 := (IH (n - 1 - p) (by omega)).2.1
          have hstep1 := (IH (n - 1 - p) (by omega)).1
          obtain ⟨b', hb'step, hb'AS⟩ := AgreeShift.step hR1 hReg1 hstep1
          have hstepn1 := (IH (n - 1) (by omega)).1
          have hb'eq : b' = g n := by
            have := Option.some.inj (hb'step.symm.trans hstepn1)
            rw [this, show n - 1 + 1 = n from by omega]
          rw [show n - 1 - p + 1 = n - p from by omega, hb'eq] at hb'AS
          exact hb'AS
        · -- `n = 2p`: the recorded base.
          have hn2 : n = 2 * p := by omega
          have e1 : g n = f (2 * p) := by rw [hn2]; exact gf (2 * p) (by omega)
          have e2 : g (n - p) = f p := by
            rw [hn2, show 2 * p - p = p from by omega]; exact gf p (by omega)
          rw [e1, e2]; exact hbase
      have hReg : Reg (g n).pos := by
        rcases Nat.lt_or_ge (2 * p) n with _ | hle
        · rw [(hAS (by omega)).2.1]
          exact hRegClosed _ ((IH (n - p) (by omega)).2.1)
        · rw [gf n (by omega)]; exact hregf2 n (by omega)
      have hStep : step? M (g n) = some (g (n + 1)) := by
        rcases Nat.lt_or_ge n (2 * p) with hlt | hge
        · rw [gf n (by omega), hrun n (by omega), gf (n + 1) (by omega)]
        · have hASn := hAS hge
          obtain ⟨b', hb'step, _⟩ :=
            AgreeShift.step hASn ((IH (n - p) (by omega)).2.1) ((IH (n - p) (by omega)).1)
          have hgb : g (n + 1) = b' := by rw [g_succ, hb'step, Option.getD_some]
          rw [hgb]; exact hb'step
      exact ⟨hStep, hReg, hAS⟩
  -- An infinite `step?`-run is a genuine infinite machine run.
  have hmulti : ∀ n, (g 0).cfg -[M]{n}-> (g n).cfg := by
    intro n
    induction n with
    | zero => exact .refl
    | succ n ih => exact Machine.Multistep.tail ih (step?_step (key n).1)
  intro hhalt
  obtain ⟨kf, hkf⟩ := hhalt
  have hrun' : (f 0).cfg -[M]{kf + 1}-> (g (kf + 1)).cfg := hmulti (kf + 1)
  exact Machine.halts_in.exceeds hkf (by omega) hrun'

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
  set d : ℤ := (c.f c.p).pos - (c.f 0).pos with hd
  have hp : 1 ≤ c.p := c.hp
  -- The two recorded windows.
  have hrun1 : ∀ i, i < c.p → step? M (c.f i) = some (c.f (i + 1)) :=
    fun i hi => c.traj i (by omega)
  have hrun2 : ∀ i, i < c.p → step? M (c.f (c.p + i)) = some (c.f (c.p + i + 1)) :=
    fun i hi => c.traj (c.p + i) (by omega)
  have hposd : ∀ i, i < c.p → (c.f (c.p + i)).pos = (c.f i).pos + d := by
    intro i hi
    have h := c.pos_window_const i (by omega)
    rw [Nat.add_comm c.p i]; omega
  have hwsym : ∀ i, i < c.p →
      absSym (c.f (c.p + i + 1)) ((c.f (c.p + i)).pos) = absSym (c.f (i + 1)) ((c.f i).pos) := by
    intro i hi
    obtain ⟨sym, dir, st, hg1, hg2, _, _⟩ := c.window_replay (j := i) hi
    obtain ⟨symA, dirA, stA, hgA, _, _, haA⟩ := absSym_step (c.traj i (by omega))
    obtain ⟨symB, dirB, stB, hgB, _, _, haB⟩ := absSym_step (c.traj (c.p + i) (by omega))
    have eA : absSym (c.f (i + 1)) ((c.f i).pos) = symA := by simp [haA]
    have eB : absSym (c.f (c.p + i + 1)) ((c.f (c.p + i)).pos) = symB := by simp [haB]
    have hsA : symA = sym := by
      have h := hgA.symm.trans hg1; simp only [Stmt.next.injEq] at h; exact h.1
    have hsB : symB = sym := by
      rw [show c.p + i = i + c.p from Nat.add_comm c.p i] at hgB
      have h := hgB.symm.trans hg2; simp only [Stmt.next.injEq] at h; exact h.1
    rw [eA, eB, hsA, hsB]
  -- Each window-step is a `±1` move (used by the discrete IVT).
  have hsteps : ∀ i, i < c.p - 1 →
      (c.f (i + 1)).pos = (c.f i).pos + 1 ∨ (c.f (i + 1)).pos = (c.f i).pos - 1 := by
    intro i hi
    obtain ⟨sym, dir, st, _, _, hpos, _⟩ := absSym_step (c.traj i (by omega))
    cases dir with
    | left => exact Or.inr (by rw [hpos]; rfl)
    | right => exact Or.inl (by rw [hpos]; rfl)
  have Jp := window_pair_inv hrun1 hrun2 hposd hwsym c.p (le_refl _)
  have hstate2 : (c.f (2 * c.p)).cfg.state = (c.f c.p).cfg.state := by
    have h := (c.matchSH c.p (le_refl _)).1
    rw [show c.p + c.p = 2 * c.p from by omega] at h; exact h.symm
  have hpos2 : (c.f (2 * c.p)).pos = (c.f c.p).pos + d := by
    have h2 := c.shift_eq
    rw [show LoopCert.shift c.f c.p = (c.f (2 * c.p)).pos - (c.f c.p).pos from rfl] at h2
    omega
  -- A cell that is unvisited in the first window lies strictly to one side of every visited cell.
  have houtside : ∀ x : ℤ, (∀ i, i < c.p → (c.f i).pos ≠ x) →
      (∀ i, i < c.p → x < (c.f i).pos) ∨ (∀ i, i < c.p → (c.f i).pos < x) := by
    intro x hvis
    by_contra hcon
    simp only [not_or, not_forall, not_lt] at hcon
    obtain ⟨⟨a, ha, hax⟩, ⟨b, hb', hxb⟩⟩ := hcon
    obtain ⟨k, hk, hkx⟩ :=
      int_path_bracket (q := fun i => (c.f i).pos) (K := c.p - 1) hsteps a b
        (by omega) (by omega) x hax hxb
    exact hvis k (by omega) hkx
  -- Builds the base shift relation from an "unvisited cells are blank" obligation.
  have mkbase : ∀ Reg : ℤ → Prop,
      (∀ x, Reg x → (∀ i, i < c.p → (c.f i).pos ≠ x) →
        absSym (c.f c.p) (x + d) = absSym (c.f 0) x) →
      AgreeShift d Reg (c.f (2 * c.p)) (c.f c.p) := by
    intro Reg hunv
    refine ⟨hstate2, hpos2, fun x hRx => ?_⟩
    rw [show 2 * c.p = c.p + c.p from by omega]
    by_cases hvis : ∃ i, i < c.p ∧ (c.f i).pos = x
    · exact (Jp x).1 hvis
    · have hvis' : ∀ i, i < c.p → (c.f i).pos ≠ x := fun i hi hix => hvis ⟨i, hi, hix⟩
      obtain ⟨hA, hB⟩ := (Jp x).2 hvis'
      rw [hA, hB]; exact hunv x hRx hvis'
  -- Extract the base check and split on the sign of the net shift.
  have hb := c.base
  rw [c.shift_eq, ← hd] at hb
  simp only [baseLoopCheck, beq_self_eq_true, Bool.true_and] at hb
  rcases lt_trichotomy d 0 with hdneg | hdzero | hdpos
  · -- Left translation.
    rw [if_neg (by omega : ¬ d = 0), if_neg (by omega : ¬ d > 0)] at hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨hnvl, _⟩ := hb
    simp only [noVisitedLeft, decide_eq_true_eq] at hnvl
    refine loopCert_nonHalting_aux (Reg := fun x => ∃ i, i < c.p ∧ x ≤ (c.f i).pos)
      hp c.traj (fun x => fun ⟨i, hi, hix⟩ => ⟨i, hi, by omega⟩) ?_ (mkbase _ ?_)
    · -- `hregf2`
      intro j hj
      rcases Nat.lt_or_ge j c.p with h | h
      · exact ⟨j, h, le_refl _⟩
      · rcases Nat.lt_or_ge j (2 * c.p) with h2 | h2
        · refine ⟨j - c.p, by omega, ?_⟩
          have := hposd (j - c.p) (by omega)
          rw [show c.p + (j - c.p) = j from by omega] at this; omega
        · refine ⟨0, by omega, ?_⟩
          have h0 := hposd 0 (by omega)
          rw [show c.p + 0 = c.p from by omega] at h0
          rw [show j = 2 * c.p from by omega]; omega
    · -- `hunv`
      intro x _ hvis'
      rcases houtside x hvis' with hleft | hright
      · have hx0 : x < (c.f 0).pos := hleft 0 (by omega)
        have hbx : absSym (c.f 0) x = default := absSym_of_left_blank hnvl x hx0
        have hconst := absSym_const_of_unvisited (e := c.f) (x := x + d) (a := 0) c.p
          (fun i hi => by simpa using hrun1 i hi)
          (fun i hi => by have := hleft i hi; simp only [Nat.zero_add]; omega)
        rw [show (0 : ℕ) + c.p = c.p from by omega] at hconst
        have hbxd : absSym (c.f 0) (x + d) = default := absSym_of_left_blank hnvl (x + d) (by omega)
        rw [hconst, hbxd, hbx]
      · obtain ⟨i, hi, hix⟩ := ‹∃ i, i < c.p ∧ x ≤ (c.f i).pos›
        exact absurd (hright i hi) (by omega)
  · -- Pure cycle (`d = 0`).
    refine loopCert_nonHalting_aux (Reg := fun _ => True) hp c.traj (fun _ _ => trivial)
      (fun _ _ => trivial) (mkbase _ (fun x _ hvis' => ?_))
    rw [hdzero, add_zero]; exact ((Jp x).2 hvis').2
  · -- Right translation.
    rw [if_neg (by omega : ¬ d = 0), if_pos hdpos] at hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨hnvr, _⟩ := hb
    simp only [noVisitedRight, decide_eq_true_eq] at hnvr
    refine loopCert_nonHalting_aux (Reg := fun x => ∃ i, i < c.p ∧ (c.f i).pos ≤ x)
      hp c.traj (fun x => fun ⟨i, hi, hix⟩ => ⟨i, hi, by omega⟩) ?_ (mkbase _ ?_)
    · -- `hregf2`
      intro j hj
      rcases Nat.lt_or_ge j c.p with h | h
      · exact ⟨j, h, le_refl _⟩
      · rcases Nat.lt_or_ge j (2 * c.p) with h2 | h2
        · refine ⟨j - c.p, by omega, ?_⟩
          have := hposd (j - c.p) (by omega)
          rw [show c.p + (j - c.p) = j from by omega] at this; omega
        · refine ⟨0, by omega, ?_⟩
          have h0 := hposd 0 (by omega)
          rw [show c.p + 0 = c.p from by omega] at h0
          rw [show j = 2 * c.p from by omega]; omega
    · -- `hunv`
      intro x _ hvis'
      rcases houtside x hvis' with hleft | hright
      · obtain ⟨i, hi, hix⟩ := ‹∃ i, i < c.p ∧ (c.f i).pos ≤ x›
        exact absurd (hleft i hi) (by omega)
      · have hx0 : (c.f 0).pos < x := hright 0 (by omega)
        have hbx : absSym (c.f 0) x = default := absSym_of_right_blank hnvr x hx0
        have hconst := absSym_const_of_unvisited (e := c.f) (x := x + d) (a := 0) c.p
          (fun i hi => by simpa using hrun1 i hi)
          (fun i hi => by have := hright i hi; simp only [Nat.zero_add]; omega)
        rw [show (0 : ℕ) + c.p = c.p from by omega] at hconst
        have hbxd : absSym (c.f 0) (x + d) = default := absSym_of_right_blank hnvr (x + d) (by omega)
        rw [hconst, hbxd, hbx]

/-! ### Decoding a successful `run` into a `LoopCert`

The decode side.  `gExt M ⟨init,0⟩` is the canonical run; `hbHist g k = [g (k-1), …, g 0]` is the
history list the search accumulates.  `runFrom_sound` shows a successful `run` realizes the full
forward run and reaches `findLoop10`; `findLoop1_sound`/`verifyLoop1_sound` extract the period `p`,
the step-by-step window match (`matchSH`) and the base condition. -/

/-- The history list accumulated by `runFrom`, newest first: `[g (k-1), …, g 0]`. -/
private def hbHist (g : ℕ → HistoryEntry l s) : ℕ → List (HistoryEntry l s)
  | 0 => []
  | k + 1 => g k :: hbHist g k

/-- `runFrom` soundness: a successful run is a genuine forward run reaching `findLoop10`. -/
private lemma runFrom_sound {M : Machine l s} (g : ℕ → HistoryEntry l s)
    (hg : ∀ i, g (i + 1) = (step? M (g i)).getD (g i)) :
    ∀ fuel k, runFrom M fuel (g k) (hbHist g k) = true →
      (∀ i, k ≤ i → i < k + fuel → step? M (g i) = some (g (i + 1))) ∧
      findLoop10 (g (k + fuel)) (g (k + fuel - 1)) (hbHist g (k + fuel - 1)) = true := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    match fuel with
    | 0 => intro k h; simp [runFrom] at h
    | F + 1 =>
      intro k h
      have hstep : step? M (g k) = some (g (k + 1)) := by
        cases hs : step? M (g k) with
        | none => rw [runFrom, hs] at h; simp at h
        | some w =>
            have hw : g (k + 1) = w := by rw [hg k, hs, Option.getD_some]
            rw [hw]
      rw [runFrom, hstep] at h
      simp only at h
      match F with
      | 0 =>
          refine ⟨fun i hi1 hi2 => ?_, ?_⟩
          · have : i = k := by omega
            subst this; exact hstep
          · simpa using h
      | F' + 1 =>
          have hrec : runFrom M (F' + 1) (g (k + 1)) (hbHist g (k + 1)) = true := h
          obtain ⟨hsteprec, hfloop⟩ := ih (F' + 1) (by omega) (k + 1) hrec
          refine ⟨fun i hi1 hi2 => ?_, ?_⟩
          · rcases Nat.lt_or_ge i (k + 1) with h' | h'
            · have : i = k := by omega
              subst this; exact hstep
            · exact hsteprec i h' (by omega)
          · rw [show k + (F' + 1 + 1) = k + 1 + (F' + 1) from by omega]; exact hfloop

/-- `verifyLoop1` soundness: walking the two tracks `g a, g (a-1), …` and `g b, g (b-1), …`
backward, the loop check succeeds at some depth `t ≥ m` where the base condition holds and every
aligned pair up to `t` agrees on state and head. -/
private lemma verifyLoop1_sound (g : ℕ → HistoryEntry l s) (dpos : ℤ) :
    ∀ b a m, b < a → verifyLoop1 (g a) (g b) (hbHist g a) (hbHist g b) m dpos = true →
      ∃ t, t ≤ b ∧ m ≤ t ∧ baseLoopCheck (g (a - t)) (g (b - t)) 0 dpos = true ∧
        (∀ j, j ≤ t → sameStateHead (g (a - j)) (g (b - j)) = true) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a m hab hv
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rcases b with _ | B
    · simp only [hbHist, verifyLoop1, Bool.and_eq_true] at hv
      obtain ⟨hssh, hbase⟩ := hv
      have hm : m = 0 := by
        simp only [baseLoopCheck, Bool.and_eq_true, beq_iff_eq] at hbase; exact hbase.1
      refine ⟨0, le_refl _, by omega, ?_, ?_⟩
      · simpa [hm] using hbase
      · intro j hj
        have : j = 0 := by omega
        subst this; simpa using hssh
    · simp only [hbHist, verifyLoop1, Bool.and_eq_true, Bool.or_eq_true] at hv
      obtain ⟨hssh, hrest⟩ := hv
      rcases hrest with hbase | hrec
      · have hm : m = 0 := by
          simp only [baseLoopCheck, Bool.and_eq_true, beq_iff_eq] at hbase; exact hbase.1
        refine ⟨0, by omega, by omega, ?_, ?_⟩
        · simpa [hm] using hbase
        · intro j hj
          have : j = 0 := by omega
          subst this; simpa using hssh
      · obtain ⟨t', ht'b, ht'm, ht'base, ht'ssh⟩ := ih B (by omega) a' m.pred (by omega) hrec
        rw [Nat.pred_eq_sub_one] at ht'm
        refine ⟨t' + 1, by omega, by omega, ?_, ?_⟩
        · rw [show a' + 1 - (t' + 1) = a' - t' from by omega,
              show B + 1 - (t' + 1) = B - t' from by omega]
          exact ht'base
        · intro j hj
          rcases Nat.eq_zero_or_pos j with hj0 | hj0
          · subst hj0; simpa using hssh
          · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
            rw [show a' + 1 - (j' + 1) = a' - j' from by omega,
                show B + 1 - (j' + 1) = B - j' from by omega]
            exact ht'ssh j' (by omega)

/-- `sameStateHead` decoded into the `state`/`head` equalities it asserts. -/
private lemma sameStateHead_eq {a b : HistoryEntry l s} (h : sameStateHead a b = true) :
    a.cfg.state = b.cfg.state ∧ a.cfg.tape.head = b.cfg.tape.head := by
  simp only [sameStateHead, Bool.and_eq_true, decide_eq_true_eq] at h; exact h

/-- **Displacement constancy.** Along two tracks that agree on `(state, head)` at every aligned
position, the head displacement between them is constant.  This is what makes the net shift `dpos`
read off at the front equal the certificate's `shift`. -/
private lemma dispConst {M : Machine l s} (g : ℕ → HistoryEntry l s) {bound p : ℕ}
    (hrun : ∀ i, i < bound → step? M (g i) = some (g (i + 1)))
    {t : ℕ} (ht : p + t ≤ bound)
    (hssh : ∀ j, j ≤ t → sameStateHead (g (bound - j)) (g (bound - p - j)) = true) :
    ∀ j, j ≤ t →
      (g (bound - j)).pos - (g (bound - p - j)).pos
        = (g bound).pos - (g (bound - p)).pos := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      have hstepA : step? M (g (bound - (j + 1))) = some (g (bound - j)) := by
        have hr := hrun (bound - (j + 1)) (by omega)
        rwa [show bound - (j + 1) + 1 = bound - j from by omega] at hr
      have hstepB : step? M (g (bound - p - (j + 1))) = some (g (bound - p - j)) := by
        have hr := hrun (bound - p - (j + 1)) (by omega)
        rwa [show bound - p - (j + 1) + 1 = bound - p - j from by omega] at hr
      obtain ⟨hst, hhd⟩ := sameStateHead_eq (hssh (j + 1) hj)
      obtain ⟨symA, dirA, stA, hgetA, _, hposA, _⟩ := absSym_step hstepA
      obtain ⟨symB, dirB, stB, hgetB, _, hposB, _⟩ := absSym_step hstepB
      have hdir : dirA = dirB := by
        have hget : M.get (g (bound - (j + 1))).cfg.state (g (bound - (j + 1))).cfg.tape.head
            = M.get (g (bound - p - (j + 1))).cfg.state (g (bound - p - (j + 1))).cfg.tape.head := by
          rw [hst, hhd]
        rw [hgetA, hgetB] at hget
        simp only [Stmt.next.injEq] at hget; exact hget.2.1
      rw [hdir] at hposA
      have ihv := ih (by omega)
      omega

/-- `verifyLoop1` with an empty second list and a nonzero counter never succeeds (the base check
needs the counter to be `0`, and there is no list left to recurse on). -/
private lemma verifyLoop1_nil {h0 h1 : HistoryEntry l s} {L0 : List (HistoryEntry l s)} {n : ℕ}
    {dpos : ℤ} : verifyLoop1 h0 h1 L0 [] (n + 1) dpos = false := by
  cases L0 <;> simp [verifyLoop1, baseLoopCheck]

/-- One-step unfolding of `findLoop1` when both work-lists are long enough (the first arm). -/
private lemma findLoop1_cons {h0 h1 h2 x z y : HistoryEntry l s}
    {ls0 ls1' ls2' : List (HistoryEntry l s)} {n : ℕ} :
    findLoop1 h0 h1 h2 ls0 (x :: ls1') (z :: y :: ls2') n =
      ((sameStateHead h0 h1 && sameStateHead h0 h2 &&
          verifyLoop1 h0 h1 ls0 (x :: ls1') (n + 1) (h0.pos - h1.pos)) ||
        findLoop1 h0 x y ls0 ls1' ls2' (n + 1)) := by
  rw [findLoop1]

/-- `findLoop1` is `false` whenever the search reaches its base arm (work-lists too short): that
arm verifies against an empty list with a nonzero counter, which always fails. -/
private lemma findLoop1_base_false {h0 h1 h2 : HistoryEntry l s}
    {ls0 ls1 ls2 : List (HistoryEntry l s)} {n : ℕ}
    (hbase : ls1 = [] ∨ ls2 = [] ∨ ∃ w, ls2 = [w]) :
    findLoop1 h0 h1 h2 ls0 ls1 ls2 n = false := by
  rcases hbase with rfl | rfl | ⟨w, rfl⟩
  · rw [findLoop1] <;> simp [verifyLoop1_nil]
  · cases ls1 <;> (rw [findLoop1] <;> simp [verifyLoop1_nil])
  · cases ls1 <;> (rw [findLoop1] <;> simp [verifyLoop1_nil])

/-- `findLoop1` soundness: a successful tortoise/hare search yields a period `p` for which the
verification step succeeds. -/
private lemma findLoop1_sound (g : ℕ → HistoryEntry l s) {bound : ℕ} :
    ∀ F n, bound - 1 - n ≤ F →
      findLoop1 (g bound) (g (bound - 1 - n)) (g (bound - 2 - 2 * n))
        (hbHist g bound) (hbHist g (bound - 1 - n)) (hbHist g (bound - 2 - 2 * n)) n = true →
      ∃ p, 1 ≤ p ∧ verifyLoop1 (g bound) (g (bound - p)) (hbHist g bound) (hbHist g (bound - p))
             p ((g bound).pos - (g (bound - p)).pos) = true := by
  intro F
  induction F with
  | zero =>
      intro n hF hfl
      rw [findLoop1_base_false (Or.inl (show hbHist g (bound - 1 - n) = [] from by
        rw [show bound - 1 - n = 0 from by omega]; rfl))] at hfl
      simp at hfl
  | succ F ih =>
      intro n hF hfl
      by_cases hc : 1 ≤ bound - 1 - n ∧ 2 ≤ bound - 2 - 2 * n
      · obtain ⟨hc1, hc2⟩ := hc
        obtain ⟨a1, ha1⟩ : ∃ k, bound - 1 - n = k + 1 := ⟨bound - 2 - n, by omega⟩
        obtain ⟨a2, ha2⟩ : ∃ k, bound - 2 - 2 * n = k + 2 := ⟨bound - 4 - 2 * n, by omega⟩
        have e1 : hbHist g (a1 + 1) = g a1 :: hbHist g a1 := rfl
        have e2 : hbHist g (a2 + 2) = g (a2 + 1) :: g a2 :: hbHist g a2 := rfl
        rw [ha1, ha2, e1, e2, findLoop1_cons, Bool.or_eq_true, Bool.and_eq_true,
            Bool.and_eq_true] at hfl
        rcases hfl with ⟨⟨_, _⟩, hV⟩ | hR
        · refine ⟨n + 1, by omega, ?_⟩
          rw [show bound - (n + 1) = a1 + 1 from by omega, e1]
          exact hV
        · rw [show a1 = bound - 1 - (n + 1) from by omega,
              show a2 = bound - 2 - 2 * (n + 1) from by omega] at hR
          exact ih (n + 1) (by omega) hR
      · exfalso
        have hbase : hbHist g (bound - 1 - n) = [] ∨ hbHist g (bound - 2 - 2 * n) = []
            ∨ ∃ w, hbHist g (bound - 2 - 2 * n) = [w] := by
          by_cases h1 : 1 ≤ bound - 1 - n
          · have h2 : bound - 2 - 2 * n < 2 := by
              by_contra hcon; exact hc ⟨h1, by omega⟩
            rcases Nat.lt_or_ge (bound - 2 - 2 * n) 1 with hz | ho
            · exact Or.inr (Or.inl (by rw [show bound - 2 - 2 * n = 0 from by omega]; rfl))
            · exact Or.inr (Or.inr ⟨g 0, by rw [show bound - 2 - 2 * n = 1 from by omega]; rfl⟩)
          · exact Or.inl (by rw [show bound - 1 - n = 0 from by omega]; rfl)
        rw [findLoop1_base_false hbase] at hfl
        simp at hfl

/-- `findLoop10` soundness: it just sets up the `findLoop1` search at `n = 0`. -/
private lemma findLoop10_sound (g : ℕ → HistoryEntry l s) {bound : ℕ}
    (hb2 : 2 ≤ bound)
    (h : findLoop10 (g bound) (g (bound - 1)) (hbHist g (bound - 1)) = true) :
    ∃ p, 1 ≤ p ∧ verifyLoop1 (g bound) (g (bound - p)) (hbHist g bound) (hbHist g (bound - p))
           p ((g bound).pos - (g (bound - p)).pos) = true := by
  obtain ⟨b, rfl⟩ : ∃ b, bound = b + 2 := ⟨bound - 2, by omega⟩
  rw [show hbHist g (b + 2 - 1) = g b :: hbHist g b from by
        rw [show b + 2 - 1 = b + 1 from by omega]; rfl, findLoop10,
      show b + 2 - 1 = b + 1 from by omega] at h
  refine findLoop1_sound g (b + 1) 0 (by omega) ?_
  rw [show b + 2 - 1 - 0 = b + 1 from by omega, show b + 2 - 2 - 2 * 0 = b from by omega]
  exact h

/-- **Decoding.** A successful `run` yields a `LoopCert`. -/
theorem loopCert_of_run {M : Machine l s} {bound : ℕ} (h : run bound M = true) :
    Nonempty (LoopCert M) := by
  set g := gExt M (⟨init, 0⟩ : HistoryEntry l s) with hgdef
  have hg : ∀ i, g (i + 1) = (step? M (g i)).getD (g i) := fun _ => rfl
  have hg0 : (g 0).cfg = (init : Config l s) := rfl
  have hrun0 : runFrom M bound (g 0) (hbHist g 0) = true := h
  obtain ⟨hsteps0, hfl10⟩ := runFrom_sound g hg bound 0 hrun0
  simp only [Nat.zero_add] at hsteps0 hfl10
  have hsteps : ∀ i, i < bound → step? M (g i) = some (g (i + 1)) :=
    fun i hi => hsteps0 i (Nat.zero_le i) hi
  -- the run reaches ≥ 2 configs (needed for the loop search to find a length-`p` window)
  have hb2 : 2 ≤ bound := by
    by_contra hlt
    rw [show bound - 1 = 0 from by omega, show hbHist g 0 = [] from rfl, findLoop10] at hfl10
    exact absurd hfl10 (by simp)
  obtain ⟨p, hp, hV⟩ := findLoop10_sound g hb2 hfl10
  obtain ⟨t, htb, htm, htbase, htssh⟩ :=
    verifyLoop1_sound g ((g bound).pos - (g (bound - p)).pos) (bound - p) bound p (by omega) hV
  -- multistep reachability of every visited config
  have hmulti : ∀ k, k ≤ bound → (g 0).cfg -[M]{k}-> (g k).cfg := by
    intro k
    induction k with
    | zero => intro _; exact .refl
    | succ k ih =>
        intro hk
        exact Machine.Multistep.tail (ih (by omega)) (step?_step (hsteps k (by omega)))
  -- net shift is the displacement read off at the front
  have hdisp := dispConst g hsteps (p := p) (t := t) (by omega) htssh
  refine ⟨{
    f := fun i => g (bound - p - t + i)
    p := p
    hp := hp
    reach := by
      have := (hmulti (bound - p - t) (by omega)).to_evstep
      rwa [hg0] at this
    traj := by
      intro i hi
      have := hsteps (bound - p - t + i) (by omega)
      rwa [show bound - p - t + i + 1 = bound - p - t + (i + 1) from by omega] at this
    matchSH := by
      intro j hj
      obtain ⟨hst, hhd⟩ := sameStateHead_eq (htssh (t - j) (by omega))
      rw [show bound - (t - j) = bound - p - t + (j + p) from by omega,
          show bound - p - (t - j) = bound - p - t + j from by omega] at hst hhd
      exact ⟨hst.symm, hhd.symm⟩
    base := by
      have hshift : LoopCert.shift (fun i => g (bound - p - t + i)) p
          = (g bound).pos - (g (bound - p)).pos := by
        have hd := hdisp (t - p) (by omega)
        rw [show bound - (t - p) = bound - p - t + 2 * p from by omega,
            show bound - p - (t - p) = bound - p - t + p from by omega] at hd
        simp only [LoopCert.shift]
        rw [show bound - p - t + 2 * p = bound - p - t + 2 * p from rfl]
        omega
      rw [hshift,
          show bound - p - t + p = bound - t from by omega,
          show bound - p - t + 0 = bound - p - t from by omega]
      rw [show bound - p - t = bound - p - t from rfl]
      have : bound - p - t = (bound - p) - t := by omega
      rw [this]
      exact htbase
  }⟩

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
