import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability
import Busybeaver.TM.Table.ClosedSet
import Std.Data.HashSet

open TM.Table

namespace Deciders.WFAR

inductive GapDir where
  | none
  | left
  | right
deriving DecidableEq, BEq, Hashable

def GapDir.delta : GapDir → Int
  | .none => 0
  | .left => -1
  | .right => 1

def dirDelta : Turing.Dir → Int
  | .left => -1
  | .right => 1

abbrev WTrans := (Nat × Int) × (Nat × Int)

structure WDFA where
  states : Nat
  trans : Array WTrans

structure Config where
  maxD : Nat
  left : WDFA
  right : WDFA
  bound : Nat

structure ES where
  leftState : Nat
  rightState : Nat
  head : Symbol 1
  state : Label 4
  diff : Int
  gap : GapDir
deriving DecidableEq, Hashable

-- We give `ES` a `BEq` that decides structural equality (rather than the derived
-- field-by-field `BEq`) so that it is `LawfulBEq`/`EquivBEq`; this is needed to reason
-- about the `Std.HashSet ES` used by the search. The runtime behaviour is unchanged
-- (both decide structural equality), so it does not affect the deciders.
instance : BEq ES := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq ES where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl {a} := by simp [BEq.beq]

instance : LawfulHashable ES where
  hash_eq {a b} h := by rw [eq_of_beq h]

abbrev ESSet := Std.HashSet ES
abbrev NatSet := Std.HashSet Nat

def WDFA.uList (w : WDFA) : List Nat :=
  List.range (w.states + 1)

def symbols : List (Symbol 1) :=
  List.finRange 2

def WDFA.step (w : WDFA) (u : Nat) (sym : Symbol 1) : Nat × Int :=
  let pair := w.trans.getD u ((0, 0), (0, 0))
  if sym.val = 0 then pair.1 else pair.2

def WDFA.pop (w : WDFA) (target : Nat) : List (Nat × Symbol 1 × Int) :=
  symbols.flatMap fun sym =>
    w.uList.filterMap fun u =>
      let step := w.step u sym
      if step.1 = target then
        some (u, sym, step.2)
      else
        none

def insertNat (x : Nat) (set : NatSet) : NatSet × Bool :=
  if set.contains x then
    (set, false)
  else
    (set.insert x, true)

def insertES (x : ES) (set : ESSet) (queue : List ES) : ESSet × List ES :=
  if set.contains x then
    (set, queue)
  else
    (set.insert x, x :: queue)

def wdfaSgnStep (w : WDFA) (dir : Turing.Dir) (set : NatSet) : NatSet × Bool :=
  Id.run do
    let mut cur := set
    let mut changed := false
    for u0 in w.uList do
      for sym in symbols do
        let step := w.step u0 sym
        if step.2 * dirDelta dir >= 0 && !(cur.contains u0) then
          cur := cur
        else
          let (next, inserted) := insertNat step.1 cur
          cur := next
          changed := changed || inserted
    (cur, changed)

def wdfaSgnSet : Nat → WDFA → Turing.Dir → NatSet → NatSet
  | 0, _, _, set => set
  | fuel + 1, w, dir, set =>
      let (next, changed) := wdfaSgnStep w dir set
      if changed then
        wdfaSgnSet fuel w dir next
      else
        next

def wdfaSgn (fuel : Nat) (w : WDFA) (dir : Turing.Dir) (u : Nat) : Bool :=
  !(wdfaSgnSet fuel w dir (Std.HashSet.emptyWithCapacity 128)).contains u

def wdfa0 (w : WDFA) : Bool :=
  w.step 0 (0 : Symbol 1) == (0, 0)

-- Soundness: every WDFA transition stays within the state range `{0, …, states}`,
-- so that the WDFA state of any tape is always a valid state in `uList`.
def wdfaRangeClosed (w : WDFA) : Bool :=
  w.uList.all fun u0 =>
    symbols.all fun sym =>
      decide ((w.step u0 sym).1 < w.states + 1)

def wdfaSgnClosed (fuel : Nat) (w : WDFA) (dir : Turing.Dir) : Bool :=
  w.uList.all fun u0 =>
    if wdfaSgn fuel w dir u0 then
      w.uList.all fun u1 =>
        symbols.all fun sym =>
          let step := w.step u1 sym
          if step.1 = u0 then
            step.2 * dirDelta dir >= 0 && wdfaSgn fuel w dir u1
          else
            true
    else
      true

def good (sgnL sgnR : Turing.Dir → Nat → Bool) (es : ES) : Bool :=
  !(
    (es.diff > 0 && es.gap.delta >= 0 && sgnL .left es.leftState && sgnR .left es.rightState) ||
    (es.diff < 0 && es.gap.delta <= 0 && sgnL .right es.leftState && sgnR .right es.rightState)
  )

def simplify (cfg : Config) (es : ES) : List ES :=
  match es.gap with
  | .none =>
      if es.diff.natAbs >= cfg.maxD then
        if es.diff > 0 then
          [{ es with gap := .right }]
        else if es.diff < 0 then
          [{ es with gap := .left }]
        else
          [es]
      else
        [es]
  | gap =>
      let absd := es.diff.natAbs
      if absd > cfg.maxD then
        [{ es with diff := es.diff - gap.delta }]
      else if absd < cfg.maxD then
        [{ es with gap := .none }, { es with diff := es.diff + gap.delta }]
      else
        [es]

def filterSimplify (cfg : Config)
    (sgnL sgnR : Turing.Dir → Nat → Bool) (states : List ES) : List ES :=
  states.filter (good sgnL sgnR) |>.flatMap (simplify cfg)

def successors (cfg : Config) (M : Machine 4 1)
    (sgnL sgnR : Turing.Dir → Nat → Bool) (es : ES) : Option (List ES) :=
  match M.get es.state es.head with
  | .halt => none
  | .next out .right state' =>
      let leftStep := cfg.left.step es.leftState out
      let candidates :=
        (cfg.right.pop es.rightState).map fun (rightState', head', dr) =>
          {
            leftState := leftStep.1
            rightState := rightState'
            head := head'
            state := state'
            diff := es.diff + leftStep.2 - dr
            gap := es.gap
          }
      some (filterSimplify cfg sgnL sgnR candidates)
  | .next out .left state' =>
      let rightStep := cfg.right.step es.rightState out
      let candidates :=
        (cfg.left.pop es.leftState).map fun (leftState', head', dl) =>
          {
            leftState := leftState'
            rightState := rightStep.1
            head := head'
            state := state'
            diff := es.diff + rightStep.2 - dl
            gap := es.gap
          }
      some (filterSimplify cfg sgnL sgnR candidates)

def insertAll (items : List ES) (seen : ESSet) (queue : List ES) : ESSet × List ES :=
  items.foldl (fun (acc : ESSet × List ES) item => insertES item acc.1 acc.2) (seen, queue)

def search (cfg : Config) (M : Machine 4 1)
    (sgnL sgnR : Turing.Dir → Nat → Bool) : Nat → List ES → ESSet → Bool
  | 0, queue, _ => queue.isEmpty
  | _ + 1, [], _ => true
  | fuel + 1, es :: queue, seen =>
      match successors cfg M sgnL sgnR es with
      | none => false
      | some next =>
          let (seen', queue') := insertAll next seen queue
          search cfg M sgnL sgnR fuel queue' seen'

def initES : ES := {
  leftState := 0
  rightState := 0
  head := 0
  state := default
  diff := 0
  gap := .none
}

def initSeen : ESSet := (Std.HashSet.emptyWithCapacity 4096).insert initES

def run (cfg : Config) (M : Machine 4 1) : Bool :=
  wdfa0 cfg.left && wdfa0 cfg.right &&
    wdfaRangeClosed cfg.left && wdfaRangeClosed cfg.right &&
    wdfaSgnClosed cfg.bound cfg.left .left && wdfaSgnClosed cfg.bound cfg.left .right &&
    wdfaSgnClosed cfg.bound cfg.right .left && wdfaSgnClosed cfg.bound cfg.right .right &&
    search cfg M (wdfaSgn cfg.bound cfg.left) (wdfaSgn cfg.bound cfg.right)
      cfg.bound [initES] initSeen

/-! ### Correctness of the WFAR decider

We show that whenever `run cfg M = true`, the machine `M` does not halt from the
initial configuration.  The certificate describes two weighted DFAs (`cfg.left` and
`cfg.right`) reading the two halves of the tape.  Reading a half-tape accumulates a
final state together with an integer weight.  An abstract execution state `ES`
represents a TM configuration `C` when the WDFA states/head/control state match and
the abstract `diff`/`gap` bound the total accumulated weight (`InMITM` below, the
analogue of CoqBB5's `In_MITM_WDFA_ES`).

The BFS `search` explores abstract states; if it succeeds, the set of explored states
is *closed* under the abstract step relation and contains the initial abstract state.
Pulling this back through `InMITM` yields a `ClosedSet` of real configurations, hence
non-halting. -/

namespace Correctness

/-- A TM configuration of the relevant shape. -/
abbrev TMConfig := TM.Table.Config 4 1

/-- One fold step of a weighted DFA: from accumulator `(u, z)` read symbol `a`,
move to state `(w.step u a).1` and add the weight `(w.step u a).2`. -/
def stepFold (w : WDFA) (a : Symbol 1) (acc : Nat × Int) : Nat × Int :=
  let s := w.step acc.1 a
  (s.1, acc.2 + s.2)

/-- Weighted-DFA reading of a half-tape `L` from far away towards the head, returning
the reached state and the accumulated weight.  The hypothesis `h0` (the WDFA fixes
state `0` with weight `0` on the blank symbol) makes this well-defined on the
trailing-blank quotient. -/
def matchT (w : WDFA) (h0 : w.step 0 (0 : Symbol 1) = (0, 0))
    (L : Turing.ListBlank (Symbol 1)) : Nat × Int :=
  L.liftOn (fun l => l.foldr (stepFold w) (0, 0)) (by
    have hrep : ∀ n : ℕ, (List.replicate n (default : Symbol 1)).foldr (stepFold w) (0, 0)
        = (0, 0) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [List.replicate_succ, List.foldr_cons, ih]
          simpa [stepFold] using h0
    rintro a b ⟨n, rfl⟩
    simp only [List.foldr_append, hrep])

@[simp] lemma matchT_mk (w : WDFA) (h0 : w.step 0 (0 : Symbol 1) = (0, 0))
    (l : List (Symbol 1)) :
    matchT w h0 (Turing.ListBlank.mk l) = l.foldr (stepFold w) (0, 0) := rfl

lemma matchT_cons (w : WDFA) (h0 : w.step 0 (0 : Symbol 1) = (0, 0))
    (a : Symbol 1) (L : Turing.ListBlank (Symbol 1)) :
    matchT w h0 (L.cons a) = stepFold w a (matchT w h0 L) := by
  induction L using Turing.ListBlank.induction_on with
  | _ l => simp [Turing.ListBlank.cons_mk]

lemma matchT_default (w : WDFA) (h0 : w.step 0 (0 : Symbol 1) = (0, 0)) :
    matchT w h0 (default : Turing.ListBlank (Symbol 1)) = (0, 0) := rfl

/-- Splitting a half-tape into head and tail: reading `L` equals reading its tail and
then the head symbol. -/
lemma matchT_consHeadTail (w : WDFA) (h0 : w.step 0 (0 : Symbol 1) = (0, 0))
    (L : Turing.ListBlank (Symbol 1)) :
    stepFold w L.head (matchT w h0 L.tail) = matchT w h0 L := by
  conv_rhs => rw [← Turing.ListBlank.cons_head_tail L]
  rw [matchT_cons]

/-- The WDFA state read off any half-tape stays within the valid range. -/
lemma matchT_fst_lt (w : WDFA) (h0 : w.step 0 (0 : Symbol 1) = (0, 0))
    (hrange : ∀ u, u < w.states + 1 → ∀ i, (w.step u i).1 < w.states + 1)
    (L : Turing.ListBlank (Symbol 1)) : (matchT w h0 L).1 < w.states + 1 := by
  induction L using Turing.ListBlank.induction_on with
  | _ l =>
    simp only [matchT_mk]
    induction l with
    | nil => exact Nat.succ_pos _
    | cons a t ih =>
        rw [List.foldr_cons]
        exact hrange _ ih a

/-- The abstract facts guaranteed by the boolean guards of `run`. -/
structure Conds (cfg : Config) : Prop where
  h0L : cfg.left.step 0 (0 : Symbol 1) = (0, 0)
  h0R : cfg.right.step 0 (0 : Symbol 1) = (0, 0)
  rangeL : ∀ u, u < cfg.left.states + 1 → ∀ i, (cfg.left.step u i).1 < cfg.left.states + 1
  rangeR : ∀ u, u < cfg.right.states + 1 → ∀ i, (cfg.right.step u i).1 < cfg.right.states + 1
  sgnClosedL : ∀ (dir : Turing.Dir) (u0 : Nat), u0 < cfg.left.states + 1 →
    wdfaSgn cfg.bound cfg.left dir u0 = true →
    ∀ (u1 : Nat), u1 < cfg.left.states + 1 → ∀ (sym : Symbol 1),
    (cfg.left.step u1 sym).1 = u0 →
    (cfg.left.step u1 sym).2 * dirDelta dir ≥ 0 ∧ wdfaSgn cfg.bound cfg.left dir u1 = true
  sgnClosedR : ∀ (dir : Turing.Dir) (u0 : Nat), u0 < cfg.right.states + 1 →
    wdfaSgn cfg.bound cfg.right dir u0 = true →
    ∀ (u1 : Nat), u1 < cfg.right.states + 1 → ∀ (sym : Symbol 1),
    (cfg.right.step u1 sym).1 = u0 →
    (cfg.right.step u1 sym).2 * dirDelta dir ≥ 0 ∧ wdfaSgn cfg.bound cfg.right dir u1 = true

lemma wdfa0_decode {w : WDFA} (h : wdfa0 w = true) : w.step 0 (0 : Symbol 1) = (0, 0) := by
  rw [wdfa0] at h
  exact eq_of_beq h

lemma rangeClosed_decode {w : WDFA} (h : wdfaRangeClosed w = true) :
    ∀ u, u < w.states + 1 → ∀ i, (w.step u i).1 < w.states + 1 := by
  intro u hu i
  rw [wdfaRangeClosed] at h
  have h1 := (List.all_eq_true.mp h) u (by rw [WDFA.uList, List.mem_range]; exact hu)
  have h2 := (List.all_eq_true.mp h1) i (List.mem_finRange i)
  exact of_decide_eq_true h2

lemma sgnClosed_decode {bound : Nat} {w : WDFA} {dir : Turing.Dir}
    (h : wdfaSgnClosed bound w dir = true)
    {u0 : Nat} (hu0 : u0 < w.states + 1) (hsgn0 : wdfaSgn bound w dir u0 = true)
    {u1 : Nat} (hu1 : u1 < w.states + 1) (sym : Symbol 1)
    (hstep : (w.step u1 sym).1 = u0) :
    (w.step u1 sym).2 * dirDelta dir ≥ 0 ∧ wdfaSgn bound w dir u1 = true := by
  rw [wdfaSgnClosed] at h
  have h1 := (List.all_eq_true.mp h) u0 (by rw [WDFA.uList, List.mem_range]; exact hu0)
  rw [if_pos hsgn0] at h1
  have h2 := (List.all_eq_true.mp h1) u1 (by rw [WDFA.uList, List.mem_range]; exact hu1)
  have h3 := (List.all_eq_true.mp h2) sym (List.mem_finRange sym)
  simp only [hstep, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le] at h3
  exact h3

/-- Weighted-DFA sign soundness (analogue of CoqBB5's `wdfa_sgn_spec`): if the WDFA
state read off `L` is flagged with sign `dir`, then the accumulated weight has the
matching sign. -/
lemma matchT_sgn {bound : Nat} {w : WDFA} {dir : Turing.Dir}
    (h0 : w.step 0 (0 : Symbol 1) = (0, 0))
    (hrange : ∀ u, u < w.states + 1 → ∀ i, (w.step u i).1 < w.states + 1)
    (hclosed : ∀ (u0 : Nat), u0 < w.states + 1 → wdfaSgn bound w dir u0 = true →
       ∀ (u1 : Nat), u1 < w.states + 1 → ∀ (sym : Symbol 1), (w.step u1 sym).1 = u0 →
       (w.step u1 sym).2 * dirDelta dir ≥ 0 ∧ wdfaSgn bound w dir u1 = true)
    (L : Turing.ListBlank (Symbol 1)) :
    wdfaSgn bound w dir (matchT w h0 L).1 = true → (matchT w h0 L).2 * dirDelta dir ≥ 0 := by
  induction L using Turing.ListBlank.induction_on with
  | _ l =>
    induction l with
    | nil => intro _; simp [matchT_mk]
    | cons a t ih =>
        intro hsgn
        rw [← Turing.ListBlank.cons_mk, matchT_cons] at hsgn ⊢
        set p := matchT w h0 (Turing.ListBlank.mk t) with hp
        simp only [stepFold] at hsgn ⊢
        have hp1 : p.1 < w.states + 1 := by rw [hp]; exact matchT_fst_lt w h0 hrange _
        have hu' : (w.step p.1 a).1 < w.states + 1 := hrange p.1 hp1 a
        obtain ⟨ha', hsgnp⟩ := hclosed (w.step p.1 a).1 hu' hsgn p.1 hp1 a rfl
        have hd1 : p.2 * dirDelta dir ≥ 0 := ih hsgnp
        rw [Int.add_mul]
        exact Int.add_nonneg hd1 ha'

/-- `InMITM cfg cd C es`: the abstract execution state `es` represents the TM
configuration `C` (analogue of CoqBB5's `In_MITM_WDFA_ES`).  The two WDFA states, the
head symbol and the control state match, and `diff`/`gap` bound the total weight read
off the two halves of the tape. -/
def InMITM (cfg : Config) (cd : Conds cfg) (C : TMConfig) (es : ES) : Prop :=
  (matchT cfg.left cd.h0L C.tape.left).1 = es.leftState ∧
  (matchT cfg.right cd.h0R C.tape.right).1 = es.rightState ∧
  C.tape.head = es.head ∧
  C.state = es.state ∧
  ∃ c : Nat, es.diff + es.gap.delta * (c : Int)
    = (matchT cfg.left cd.h0L C.tape.left).2 + (matchT cfg.right cd.h0R C.tape.right).2

/-- Every abstract state representing a real configuration is `good` (analogue of
CoqBB5's `MITM_WDFA_ES_good_spec`); hence the `good` filter never drops a state that
represents a reachable configuration. -/
lemma good_spec {cfg : Config} (cd : Conds cfg) {C : TMConfig} {es : ES}
    (hin : InMITM cfg cd C es) :
    good (wdfaSgn cfg.bound cfg.left) (wdfaSgn cfg.bound cfg.right) es = true := by
  obtain ⟨hL, hR, _, _, c, hc⟩ := hin
  set dl := (matchT cfg.left cd.h0L C.tape.left).2 with hdl
  set dr := (matchT cfg.right cd.h0R C.tape.right).2 with hdr
  -- `hc : es.diff + es.gap.delta * c = dl + dr`
  have hcge : (0 : Int) ≤ (c : Int) := Int.natCast_nonneg c
  rw [good, Bool.not_eq_true', Bool.or_eq_false_iff]
  constructor
  · -- first disjunct is false
    rw [← Bool.not_eq_true]
    intro hD
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hD
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hD
    have hdiff : es.diff > 0 := of_decide_eq_true h1
    have hgap : (0 : Int) ≤ es.gap.delta := of_decide_eq_true h2
    have hdl0 : dl * dirDelta Turing.Dir.left ≥ 0 :=
      matchT_sgn cd.h0L cd.rangeL (cd.sgnClosedL Turing.Dir.left) C.tape.left (by rw [hL]; exact h3)
    have hdr0 : dr * dirDelta Turing.Dir.left ≥ 0 :=
      matchT_sgn cd.h0R cd.rangeR (cd.sgnClosedR Turing.Dir.left) C.tape.right (by rw [hR]; exact h4)
    simp only [dirDelta] at hdl0 hdr0
    have hge : (0 : Int) ≤ es.gap.delta * (c : Int) := Int.mul_nonneg hgap hcge
    omega
  · -- second disjunct is false
    rw [← Bool.not_eq_true]
    intro hD
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hD
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hD
    have hdiff : es.diff < 0 := of_decide_eq_true h1
    have hgap : es.gap.delta ≤ 0 := of_decide_eq_true h2
    have hdl0 : dl * dirDelta Turing.Dir.right ≥ 0 :=
      matchT_sgn cd.h0L cd.rangeL (cd.sgnClosedL Turing.Dir.right) C.tape.left (by rw [hL]; exact h3)
    have hdr0 : dr * dirDelta Turing.Dir.right ≥ 0 :=
      matchT_sgn cd.h0R cd.rangeR (cd.sgnClosedR Turing.Dir.right) C.tape.right (by rw [hR]; exact h4)
    simp only [dirDelta] at hdl0 hdr0
    have hng : (0 : Int) ≤ -es.gap.delta := by omega
    have hprod : (0 : Int) ≤ (-es.gap.delta) * (c : Int) := Int.mul_nonneg hng hcge
    have key : es.gap.delta * (c : Int) = -((-es.gap.delta) * (c : Int)) := by
      rw [Int.neg_mul, Int.neg_neg]
    omega

/-- Changing the `diff` field of an abstract state, keeping the diff equation valid,
preserves the abstraction. -/
lemma inMITM_setDiff {cfg : Config} {cd : Conds cfg} {C : TMConfig} {es : ES}
    (hin : InMITM cfg cd C es) (d : Int)
    (hd : ∃ cc : Nat, d + es.gap.delta * (cc : Int)
      = (matchT cfg.left cd.h0L C.tape.left).2 + (matchT cfg.right cd.h0R C.tape.right).2) :
    InMITM cfg cd C { es with diff := d } :=
  ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2.1, hd⟩

/-- Changing the `gap` field of an abstract state, keeping the diff equation valid,
preserves the abstraction. -/
lemma inMITM_setGap {cfg : Config} {cd : Conds cfg} {C : TMConfig} {es : ES}
    (hin : InMITM cfg cd C es) (g : GapDir)
    (hd : ∃ cc : Nat, es.diff + g.delta * (cc : Int)
      = (matchT cfg.left cd.h0L C.tape.left).2 + (matchT cfg.right cd.h0R C.tape.right).2) :
    InMITM cfg cd C { es with gap := g } :=
  ⟨hin.1, hin.2.1, hin.2.2.1, hin.2.2.2.1, hd⟩

/-- `simplify` preserves a representing abstract state (analogue of CoqBB5's
`MITM_WDFA_ES_simplify_spec`). -/
lemma simplify_spec {cfg : Config} {cd : Conds cfg} {C : TMConfig} {es : ES}
    (hin : InMITM cfg cd C es) :
    ∃ es', InMITM cfg cd C es' ∧ es' ∈ simplify cfg es := by
  obtain ⟨hL, hR, hh, hs, c, hc⟩ := hin
  have base : InMITM cfg cd C es := ⟨hL, hR, hh, hs, c, hc⟩
  rcases hgap : es.gap with _ | _ | _
  · -- es.gap = none, so `es.gap.delta = 0` and `hc : es.diff = T`
    rw [hgap] at hc
    simp only [GapDir.delta] at hc
    simp only [simplify, hgap]
    split_ifs with h1 h2 h3
    · exact ⟨{es with gap := .right}, inMITM_setGap base .right ⟨0, by simp [GapDir.delta]; omega⟩,
        by simp⟩
    · exact ⟨{es with gap := .left}, inMITM_setGap base .left ⟨0, by simp [GapDir.delta]; omega⟩,
        by simp⟩
    · exact ⟨es, base, by simp⟩
    · exact ⟨es, base, by simp⟩
  · -- es.gap = left, `es.gap.delta = -1`
    rw [hgap] at hc
    simp only [GapDir.delta] at hc
    simp only [simplify, hgap]
    split_ifs with h1 h2
    · refine ⟨{es with diff := es.diff - GapDir.left.delta},
        inMITM_setDiff base _ ⟨c + 1, ?_⟩, by simp [hgap]⟩
      rw [hgap]; simp only [GapDir.delta]; omega
    · rcases c with _ | c0
      · exact ⟨{es with gap := .none}, inMITM_setGap base .none ⟨0, by simp [GapDir.delta]; omega⟩,
          by simp⟩
      · refine ⟨{es with diff := es.diff + GapDir.left.delta},
          inMITM_setDiff base _ ⟨c0, ?_⟩, by simp [hgap]⟩
        rw [hgap]; simp only [GapDir.delta]; omega
    · exact ⟨es, base, by simp⟩
  · -- es.gap = right, `es.gap.delta = 1`
    rw [hgap] at hc
    simp only [GapDir.delta] at hc
    simp only [simplify, hgap]
    split_ifs with h1 h2
    · refine ⟨{es with diff := es.diff - GapDir.right.delta},
        inMITM_setDiff base _ ⟨c + 1, ?_⟩, by simp [hgap]⟩
      rw [hgap]; simp only [GapDir.delta]; omega
    · rcases c with _ | c0
      · exact ⟨{es with gap := .none}, inMITM_setGap base .none ⟨0, by simp [GapDir.delta]; omega⟩,
          by simp⟩
      · refine ⟨{es with diff := es.diff + GapDir.right.delta},
          inMITM_setDiff base _ ⟨c0, ?_⟩, by simp [hgap]⟩
        rw [hgap]; simp only [GapDir.delta]; omega
    · exact ⟨es, base, by simp⟩

/-- `filterSimplify` preserves a representing abstract state (analogue of CoqBB5's
`MITM_WDFA_ES_filter_spec`): a state that represents a real configuration is `good`,
so it survives the filter, and `simplify` keeps a representative. -/
lemma filterSimplify_spec {cfg : Config} {cd : Conds cfg} {C : TMConfig} {es : ES}
    {candidates : List ES} (hin : InMITM cfg cd C es) (hmem : es ∈ candidates) :
    ∃ es', InMITM cfg cd C es' ∧
      es' ∈ filterSimplify cfg (wdfaSgn cfg.bound cfg.left) (wdfaSgn cfg.bound cfg.right) candidates := by
  obtain ⟨es', hin', hmem'⟩ := simplify_spec (cd := cd) hin
  refine ⟨es', hin', ?_⟩
  rw [filterSimplify, List.mem_flatMap]
  exact ⟨es, List.mem_filter.mpr ⟨hmem, good_spec cd hin⟩, hmem'⟩

/-- `pop` membership (analogue of CoqBB5's `WDFA_pop_spec`): every preimage of
`target` under a step from a valid state appears in `pop target`. -/
lemma pop_mem {w : WDFA} {u : Nat} {sym : Symbol 1} {target : Nat}
    (hu : u < w.states + 1) (hstep : (w.step u sym).1 = target) :
    (u, sym, (w.step u sym).2) ∈ w.pop target := by
  rw [WDFA.pop, List.mem_flatMap]
  refine ⟨sym, List.mem_finRange sym, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨u, by rw [WDFA.uList, List.mem_range]; exact hu, ?_⟩
  simp only [hstep, ↓reduceIte]

/-- Step soundness (analogue of CoqBB5's `MITM_WDFA_ES_step_spec`): if `successors`
is defined and `es` represents `C`, then `C` makes one TM step to some `C'`
represented by an element of the produced successor list. -/
lemma successors_spec {cfg : Config} {cd : Conds cfg} {M : Machine 4 1}
    {C : TMConfig} {es : ES} {ls : List ES}
    (hin : InMITM cfg cd C es)
    (hsucc : successors cfg M (wdfaSgn cfg.bound cfg.left) (wdfaSgn cfg.bound cfg.right) es
      = some ls) :
    ∃ (C' : TMConfig) (es' : ES), M.step C = some C' ∧ InMITM cfg cd C' es' ∧ es' ∈ ls := by
  obtain ⟨hL, hR, hh, hs, c, hc⟩ := hin
  rw [successors] at hsucc
  cases hget : M.get es.state es.head with
  | halt => rw [hget] at hsucc; exact absurd hsucc (by simp)
  | next out dir state' =>
      rw [hget] at hsucc
      have hgetC : M.get C.state C.tape.head = Stmt.next out dir state' := by rw [hs, hh, hget]
      cases dir with
      | right =>
          -- right move: writes `out`, pushes it onto the left, pops the right
          simp only at hsucc
          set C' : TMConfig := ⟨state', (C.tape.write out).move Turing.Dir.right⟩ with hC'
          have hstepC : M.step C = some C' := by
            have := Machine.step.some (M := M) (q := C.state) (T := C.tape) hgetC
            simpa [hC'] using this
          -- tape projections of `C'`
          have htl : C'.tape.left = C.tape.left.cons out := rfl
          have htr : C'.tape.right = C.tape.right.tail := rfl
          have hth : C'.tape.head = C.tape.right.head := rfl
          -- weighted reading of the new left tape
          have hML' : matchT cfg.left cd.h0L C'.tape.left
              = stepFold cfg.left out (matchT cfg.left cd.h0L C.tape.left) := by
            rw [htl, matchT_cons]
          rw [stepFold, hL] at hML'
          -- weighted reading of the new right tape (popped)
          have hMR : stepFold cfg.right C.tape.right.head
                (matchT cfg.right cd.h0R C.tape.right.tail)
              = matchT cfg.right cd.h0R C.tape.right :=
            matchT_consHeadTail cfg.right cd.h0R C.tape.right
          rw [stepFold] at hMR
          have hrs : (cfg.right.step (matchT cfg.right cd.h0R C.tape.right.tail).1
              C.tape.right.head).1 = es.rightState := (congrArg Prod.fst hMR).trans hR
          have hrw : (matchT cfg.right cd.h0R C.tape.right.tail).2
              + (cfg.right.step (matchT cfg.right cd.h0R C.tape.right.tail).1 C.tape.right.head).2
              = (matchT cfg.right cd.h0R C.tape.right).2 := congrArg Prod.snd hMR
          have hrt : (matchT cfg.right cd.h0R C.tape.right.tail).1 < cfg.right.states + 1 :=
            matchT_fst_lt cfg.right cd.h0R cd.rangeR _
          -- the candidate built from the popped right state
          set cand : ES :=
            { leftState := (cfg.left.step es.leftState out).1
              rightState := (matchT cfg.right cd.h0R C.tape.right.tail).1
              head := C.tape.right.head
              state := state'
              diff := es.diff + (cfg.left.step es.leftState out).2
                - (cfg.right.step (matchT cfg.right cd.h0R C.tape.right.tail).1 C.tape.right.head).2
              gap := es.gap } with hcand
          have hin_cand : InMITM cfg cd C' cand := by
            refine ⟨?_, ?_, ?_, ?_, c, ?_⟩
            · rw [hML']
            · rw [show C'.tape.right = C.tape.right.tail from htr]
            · rw [hth]
            · rfl
            · rw [hML', show C'.tape.right = C.tape.right.tail from htr]
              simp only [hcand]
              omega
          have hmem_cand : cand ∈ (cfg.right.pop es.rightState).map
              (fun x => match x with
                | (rightState', head', dr) =>
                  ({ leftState := (cfg.left.step es.leftState out).1, rightState := rightState',
                     head := head', state := state',
                     diff := es.diff + (cfg.left.step es.leftState out).2 - dr,
                     gap := es.gap } : ES)) := by
            apply List.mem_map.mpr
            exact ⟨_, pop_mem hrt hrs, rfl⟩
          obtain ⟨es'', hin'', hmem''⟩ :=
            filterSimplify_spec (cd := cd) (C := C') hin_cand hmem_cand
          refine ⟨C', es'', hstepC, hin'', ?_⟩
          rw [← Option.some.inj hsucc]
          exact hmem''
      | left =>
          -- left move: writes `out`, pushes it onto the right, pops the left
          simp only at hsucc
          set C' : TMConfig := ⟨state', (C.tape.write out).move Turing.Dir.left⟩ with hC'
          have hstepC : M.step C = some C' := by
            have := Machine.step.some (M := M) (q := C.state) (T := C.tape) hgetC
            simpa [hC'] using this
          have htl : C'.tape.left = C.tape.left.tail := rfl
          have htr : C'.tape.right = C.tape.right.cons out := rfl
          have hth : C'.tape.head = C.tape.left.head := rfl
          -- weighted reading of the new right tape
          have hMR' : matchT cfg.right cd.h0R C'.tape.right
              = stepFold cfg.right out (matchT cfg.right cd.h0R C.tape.right) := by
            rw [htr, matchT_cons]
          rw [stepFold, hR] at hMR'
          -- weighted reading of the new left tape (popped)
          have hML : stepFold cfg.left C.tape.left.head
                (matchT cfg.left cd.h0L C.tape.left.tail)
              = matchT cfg.left cd.h0L C.tape.left :=
            matchT_consHeadTail cfg.left cd.h0L C.tape.left
          rw [stepFold] at hML
          have hls : (cfg.left.step (matchT cfg.left cd.h0L C.tape.left.tail).1
              C.tape.left.head).1 = es.leftState := (congrArg Prod.fst hML).trans hL
          have hlw : (matchT cfg.left cd.h0L C.tape.left.tail).2
              + (cfg.left.step (matchT cfg.left cd.h0L C.tape.left.tail).1 C.tape.left.head).2
              = (matchT cfg.left cd.h0L C.tape.left).2 := congrArg Prod.snd hML
          have hlt : (matchT cfg.left cd.h0L C.tape.left.tail).1 < cfg.left.states + 1 :=
            matchT_fst_lt cfg.left cd.h0L cd.rangeL _
          set cand : ES :=
            { leftState := (matchT cfg.left cd.h0L C.tape.left.tail).1
              rightState := (cfg.right.step es.rightState out).1
              head := C.tape.left.head
              state := state'
              diff := es.diff + (cfg.right.step es.rightState out).2
                - (cfg.left.step (matchT cfg.left cd.h0L C.tape.left.tail).1 C.tape.left.head).2
              gap := es.gap } with hcand
          have hin_cand : InMITM cfg cd C' cand := by
            refine ⟨?_, ?_, ?_, ?_, c, ?_⟩
            · rw [show C'.tape.left = C.tape.left.tail from htl]
            · rw [hMR']
            · rw [hth]
            · rfl
            · rw [hMR', show C'.tape.left = C.tape.left.tail from htl]
              simp only [hcand]
              omega
          have hmem_cand : cand ∈ (cfg.left.pop es.leftState).map
              (fun x => match x with
                | (leftState', head', dl) =>
                  ({ leftState := leftState', rightState := (cfg.right.step es.rightState out).1,
                     head := head', state := state',
                     diff := es.diff + (cfg.right.step es.rightState out).2 - dl,
                     gap := es.gap } : ES)) := by
            apply List.mem_map.mpr
            exact ⟨_, pop_mem hlt hls, rfl⟩
          obtain ⟨es'', hin'', hmem''⟩ :=
            filterSimplify_spec (cd := cd) (C := C') hin_cand hmem_cand
          refine ⟨C', es'', hstepC, hin'', ?_⟩
          rw [← Option.some.inj hsucc]
          exact hmem''

/-! ### Soundness of the BFS closed-set search -/

/-- One step of `insertES` satisfies the monotonicity/coverage facts used to thread
the search invariant. -/
lemma insertES_props (item : ES) (seen : ESSet) (queue : List ES) :
    (∀ e, seen.contains e = true → (insertES item seen queue).1.contains e = true) ∧
    (∀ e, e ∈ queue → e ∈ (insertES item seen queue).2) ∧
    ((insertES item seen queue).1.contains item = true) ∧
    (∀ e, e ∈ (insertES item seen queue).2 → e ∈ queue ∨ e = item) ∧
    (∀ e, (insertES item seen queue).1.contains e = true →
       seen.contains e = true ∨ e ∈ (insertES item seen queue).2) := by
  unfold insertES
  split
  · rename_i hc
    exact ⟨fun e h => h, fun e h => h, hc, fun e h => Or.inl h, fun e h => Or.inl h⟩
  · refine ⟨fun e h => ?_, fun e h => List.mem_cons_of_mem _ h, ?_, fun e h => ?_,
      fun e h => ?_⟩
    · rw [Std.HashSet.contains_insert]; simp [h]
    · rw [Std.HashSet.contains_insert]; simp
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rw [Std.HashSet.contains_insert] at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inr (by rw [← eq_of_beq h]; simp)
      · exact Or.inl h

lemma insertAll_cons (item : ES) (rest : List ES) (seen : ESSet) (queue : List ES) :
    insertAll (item :: rest) seen queue
      = insertAll rest (insertES item seen queue).1 (insertES item seen queue).2 := rfl

/-- The combined invariant-threading facts about `insertAll`. -/
lemma insertAll_props (items : List ES) (seen : ESSet) (queue : List ES) :
    (∀ e, seen.contains e = true → (insertAll items seen queue).1.contains e = true) ∧
    (∀ e, e ∈ queue → e ∈ (insertAll items seen queue).2) ∧
    (∀ e, e ∈ items → (insertAll items seen queue).1.contains e = true) ∧
    (∀ e, e ∈ (insertAll items seen queue).2 → e ∈ queue ∨ e ∈ items) ∧
    (∀ e, (insertAll items seen queue).1.contains e = true →
       seen.contains e = true ∨ e ∈ (insertAll items seen queue).2) := by
  induction items generalizing seen queue with
  | nil => refine ⟨fun e h => h, fun e h => h, fun e h => absurd h (by simp), fun e h => Or.inl h,
      fun e h => Or.inl h⟩
  | cons item rest ih =>
      obtain ⟨i1, i2, i3, i4, i5⟩ := insertES_props item seen queue
      obtain ⟨m1, m2, m3, m4, m5⟩ := ih (insertES item seen queue).1 (insertES item seen queue).2
      rw [insertAll_cons]
      refine ⟨fun e h => m1 e (i1 e h), fun e h => m2 e (i2 e h), fun e h => ?_,
        fun e h => ?_, fun e h => ?_⟩
      · rcases List.mem_cons.mp h with h | h
        · subst h; exact m1 _ i3
        · exact m3 e h
      · rcases m4 e h with h | h
        · rcases i4 e h with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [h]; simp)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases m5 e h with h | h
        · rcases i5 e h with h | h
          · exact Or.inl h
          · exact Or.inr (m2 e h)
        · exact Or.inr h

/-- `es` has all its successors inside `S` (and its `successors` are defined). -/
def Closed1 (cfg : Config) (M : Machine 4 1) (sgnL sgnR : Turing.Dir → Nat → Bool)
    (es : ES) (S : ESSet) : Prop :=
  ∃ ls, successors cfg M sgnL sgnR es = some ls ∧ ∀ e', e' ∈ ls → S.contains e' = true

/-- If `search` succeeds, the set of explored abstract states is closed: there is a
predicate `P` containing the current `seen` set, such that every `P`-state has all its
successors back in `P` (in particular every `P`-state has its `successors` defined). -/
lemma search_closed (cfg : Config) (M : Machine 4 1)
    (sgnL sgnR : Turing.Dir → Nat → Bool) (fuel : Nat) :
    ∀ (queue : List ES) (seen : ESSet),
      (∀ e, e ∈ queue → seen.contains e = true) →
      (∀ e, seen.contains e = true → e ∈ queue ∨ Closed1 cfg M sgnL sgnR e seen) →
      search cfg M sgnL sgnR fuel queue seen = true →
      ∃ P : ES → Prop,
        (∀ e, seen.contains e = true → P e) ∧
        (∀ e, P e → ∃ ls, successors cfg M sgnL sgnR e = some ls ∧ ∀ e', e' ∈ ls → P e') := by
  induction fuel with
  | zero =>
      intro queue seen _ hB hsearch
      rw [search] at hsearch
      have hq : queue = [] := List.isEmpty_iff.mp hsearch
      subst hq
      refine ⟨fun e => seen.contains e = true, fun e h => h, fun e h => ?_⟩
      rcases hB e h with h' | ⟨ls, hls, hmem⟩
      · exact absurd h' (by simp)
      · exact ⟨ls, hls, hmem⟩
  | succ fuel ih =>
      intro queue seen hA hB hsearch
      cases queue with
      | nil =>
          refine ⟨fun e => seen.contains e = true, fun e h => h, fun e h => ?_⟩
          rcases hB e h with h' | ⟨ls, hls, hmem⟩
          · exact absurd h' (by simp)
          · exact ⟨ls, hls, hmem⟩
      | cons es queue0 =>
          rw [search] at hsearch
          cases hsucc : successors cfg M sgnL sgnR es with
          | none => rw [hsucc] at hsearch; exact absurd hsearch (by simp)
          | some next =>
              rw [hsucc] at hsearch
              obtain ⟨m1, m2, m3, m4, m5⟩ := insertAll_props next seen queue0
              -- the recursive call is on `(insertAll next seen queue0)`
              have hA' : ∀ e, e ∈ (insertAll next seen queue0).2 →
                  (insertAll next seen queue0).1.contains e = true := by
                intro e he
                rcases m4 e he with he | he
                · exact m1 e (hA e (List.mem_cons_of_mem _ he))
                · exact m3 e he
              have hB' : ∀ e, (insertAll next seen queue0).1.contains e = true →
                  e ∈ (insertAll next seen queue0).2 ∨
                  Closed1 cfg M sgnL sgnR e (insertAll next seen queue0).1 := by
                intro e he
                rcases m5 e he with he | he
                · rcases hB e he with hmem | ⟨ls, hls, hclosed⟩
                  · rcases List.mem_cons.mp hmem with hmem | hmem
                    · subst hmem
                      exact Or.inr ⟨next, hsucc, fun e' he' => m3 e' he'⟩
                    · exact Or.inl (m2 e hmem)
                  · exact Or.inr ⟨ls, hls, fun e' he' => m1 e' (hclosed e' he')⟩
                · exact Or.inl he
              obtain ⟨P, hP1, hP2⟩ := ih (insertAll next seen queue0).2 (insertAll next seen queue0).1
                hA' hB' hsearch
              exact ⟨P, fun e h => hP1 e (m1 e h), hP2⟩

/-! ### Initial configuration -/

/-- The initial abstract state represents the initial TM configuration. -/
lemma inMITM_init {cfg : Config} (cd : Conds cfg) : InMITM cfg cd TM.Table.init initES := by
  have hl : (TM.Table.init : TMConfig).tape.left = (default : Turing.ListBlank (Symbol 1)) := rfl
  have hr : (TM.Table.init : TMConfig).tape.right = (default : Turing.ListBlank (Symbol 1)) := rfl
  refine ⟨?_, ?_, ?_, ?_, 0, ?_⟩
  · rw [hl]; simp [matchT_default, initES]
  · rw [hr]; simp [matchT_default, initES]
  · rfl
  · rfl
  · rw [hl, hr]; simp [matchT_default, initES, GapDir.delta]

lemma initSeen_contains_init : initSeen.contains initES = true := by
  rw [initSeen, Std.HashSet.contains_insert]; simp

lemma initSeen_mem {e : ES} (h : initSeen.contains e = true) : e = initES := by
  rw [initSeen, Std.HashSet.contains_insert] at h
  simp only [Std.HashSet.contains_emptyWithCapacity, Bool.or_false] at h
  exact (eq_of_beq h).symm

/-- Assembled non-halting proof: from a successful `search` and the decoded conditions,
the set of configurations represented by an explored abstract state is closed and
contains the initial configuration. -/
theorem nonhalting_of {cfg : Config} (cd : Conds cfg) (M : Machine 4 1)
    (hsearch : search cfg M (wdfaSgn cfg.bound cfg.left) (wdfaSgn cfg.bound cfg.right)
      cfg.bound [initES] initSeen = true) :
    ¬ M.halts TM.Table.init := by
  -- the initial search invariants
  have hA0 : ∀ e, e ∈ [initES] → initSeen.contains e = true := by
    intro e he; rw [List.mem_singleton] at he; subst he; exact initSeen_contains_init
  have hB0 : ∀ e, initSeen.contains e = true →
      e ∈ [initES] ∨ Closed1 cfg M (wdfaSgn cfg.bound cfg.left) (wdfaSgn cfg.bound cfg.right)
        e initSeen := by
    intro e he; exact Or.inl (by rw [List.mem_singleton]; exact initSeen_mem he)
  obtain ⟨P, hP1, hP2⟩ :=
    search_closed cfg M _ _ cfg.bound [initES] initSeen hA0 hB0 hsearch
  have hPinit : P initES := hP1 initES initSeen_contains_init
  suffices hcs : ClosedSet M (fun C => ∃ es, P es ∧ InMITM cfg cd C es) TM.Table.init from
    hcs.nonHalting
  refine ⟨?_, ?_⟩
  · rintro ⟨A, esA, hPA, hinA⟩
    obtain ⟨ls, hls, hclosed⟩ := hP2 esA hPA
    obtain ⟨A', es', hstep, hinA', hmem'⟩ := successors_spec (cd := cd) hinA hls
    exact ⟨⟨A', es', hclosed es' hmem', hinA'⟩, Machine.Progress.single hstep⟩
  · exact ⟨⟨TM.Table.init, initES, hPinit, inMITM_init cd⟩, Machine.EvStep.refl⟩

end Correctness

private theorem run_eq_true_nonHalting
    (cfg : Config) (M : Machine 4 1)
    (h : run cfg M = true) :
    ¬M.halts TM.Table.init := by
  rw [run] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, hs⟩ := h
  have cd : Correctness.Conds cfg :=
    { h0L := Correctness.wdfa0_decode h1
      h0R := Correctness.wdfa0_decode h2
      rangeL := Correctness.rangeClosed_decode h3
      rangeR := Correctness.rangeClosed_decode h4
      sgnClosedL := fun dir => match dir with
        | .left => fun _ hu0 hsgn0 _ hu1 sym hstep =>
            Correctness.sgnClosed_decode h5 hu0 hsgn0 hu1 sym hstep
        | .right => fun _ hu0 hsgn0 _ hu1 sym hstep =>
            Correctness.sgnClosed_decode h6 hu0 hsgn0 hu1 sym hstep
      sgnClosedR := fun dir => match dir with
        | .left => fun _ hu0 hsgn0 _ hu1 sym hstep =>
            Correctness.sgnClosed_decode h7 hu0 hsgn0 hu1 sym hstep
        | .right => fun _ hu0 hsgn0 _ hu1 sym hstep =>
            Correctness.sgnClosed_decode h8 hu0 hsgn0 hu1 sym hstep }
  exact Correctness.nonhalting_of cd M hs

def decider (cfg : Config) (M : Machine 4 1) : HaltM M Unit :=
  if h : run cfg M = true then
    .loops_prf (run_eq_true_nonHalting cfg M h)
  else
    .unknown ()

end Deciders.WFAR
