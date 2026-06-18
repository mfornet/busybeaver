import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability
import Busybeaver.TM.Table.ClosedSet
import Std.Data.HashSet

open TM.Table

namespace Deciders.FAR

abbrev U := Nat
abbrev OStU := Option (Label 4 × U)
abbrev NFAEntry := OStU × Symbol 1 × OStU
abbrev NFASet := Std.HashSet Nat
abbrev AccSet := Std.HashSet Nat

structure Config where
  states : Nat
  dfa : Array (Nat × Nat)

def Config.uList (cfg : Config) : List U :=
  List.range (cfg.states + 1)

def labels : List (Label 4) :=
  List.finRange 5

def symbols : List (Symbol 1) :=
  List.finRange 2

def optionStates (cfg : Config) : List OStU :=
  none :: (labels.flatMap fun st => cfg.uList.map fun u => some (st, u))

def Config.step (cfg : Config) (u : U) (sym : Symbol 1) : U :=
  let pair := cfg.dfa.getD u (0, 0)
  if sym.val = 0 then pair.1 else pair.2

def optionCount (cfg : Config) : Nat :=
  1 + 5 * (cfg.states + 1)

def encodeOStU (cfg : Config) : OStU → Nat
  | none => 0
  | some (st, u) => 1 + st.val * (cfg.states + 1) + u

def encodeEntry (cfg : Config) (entry : NFAEntry) : Nat :=
  let src := encodeOStU cfg entry.1
  let sym := entry.2.1.val
  let dst := encodeOStU cfg entry.2.2
  (src * 2 + sym) * optionCount cfg + dst

def nfaContains (cfg : Config) (nfa : NFASet) (entry : NFAEntry) : Bool :=
  nfa.contains (encodeEntry cfg entry)

def accContains (cfg : Config) (acc : AccSet) (state : OStU) : Bool :=
  acc.contains (encodeOStU cfg state)

def insertEntry (cfg : Config) (entry : NFAEntry) (nfa : NFASet) : NFASet × Bool :=
  let key := encodeEntry cfg entry
  if nfa.contains key then
    (nfa, false)
  else
    (nfa.insert key, true)

def insertAcc (cfg : Config) (state : OStU) (acc : AccSet) : AccSet × Bool :=
  let key := encodeOStU cfg state
  if acc.contains key then
    (acc, false)
  else
    (acc.insert key, true)

def initialNFA (cfg : Config) (M : Machine 4 1) : NFASet :=
  Id.run do
    let mut nfa : NFASet := Std.HashSet.emptyWithCapacity 4096
    for i0 in symbols do
      nfa := (insertEntry cfg (none, i0, none) nfa).1
    for s0 in labels do
      for u0 in cfg.uList do
        for i0 in symbols do
          match M.get s0 i0 with
          | .halt =>
              nfa := (insertEntry cfg (some (s0, u0), i0, none) nfa).1
          | _ => nfa := nfa
    for s0 in labels do
      for i0 in symbols do
        match M.get s0 i0 with
        | .next i1 .right s1 =>
            for u0 in cfg.uList do
              nfa := (insertEntry cfg (some (s0, u0), i0, some (s1, cfg.step u0 i1)) nfa).1
        | _ => nfa := nfa
    nfa

def closeLeftStep (cfg : Config) (M : Machine 4 1) (nfa : NFASet) : NFASet × Bool :=
  Id.run do
    let mut cur := nfa
    let mut changed := false
    for s0 in labels do
      for i0 in symbols do
        match M.get s0 i0 with
        | .next i1 .left s1 =>
            for u1 in cfg.uList do
              for i2 in symbols do
                for su2 in optionStates cfg do
                  if nfaContains cfg cur (some (s1, u1), i2, su2) then
                    for su3 in optionStates cfg do
                      if nfaContains cfg cur (su2, i1, su3) then
                        let entry := (some (s0, cfg.step u1 i2), i0, su3)
                        let (next, inserted) := insertEntry cfg entry cur
                        cur := next
                        changed := changed || inserted
        | _ => cur := cur
    (cur, changed)

def closeLeft : Nat → Config → Machine 4 1 → NFASet → NFASet
  | 0, _, _, nfa => nfa
  | fuel + 1, cfg, M, nfa =>
      let (next, changed) := closeLeftStep cfg M nfa
      if changed then
        closeLeft fuel cfg M next
      else
        next

def buildNFA (maxT : Nat) (cfg : Config) (M : Machine 4 1) : NFASet :=
  closeLeft maxT cfg M (initialNFA cfg M)

def closeAccStep (cfg : Config) (nfa : NFASet) (acc : AccSet) : AccSet × Bool :=
  Id.run do
    let mut cur := acc
    let mut changed := false
    for su0 in optionStates cfg do
      for su1 in optionStates cfg do
        if nfaContains cfg nfa (su0, (0 : Symbol 1), su1) && accContains cfg cur su0 then
          let (next, inserted) := insertAcc cfg su1 cur
          cur := next
          changed := changed || inserted
    (cur, changed)

def closeAcc : Nat → Config → NFASet → AccSet → AccSet
  | 0, _, _, acc => acc
  | fuel + 1, cfg, nfa, acc =>
      let (next, changed) := closeAccStep cfg nfa acc
      if changed then
        closeAcc fuel cfg nfa next
      else
        next

def buildAcc (maxT : Nat) (cfg : Config) (nfa : NFASet) : AccSet :=
  let initial : AccSet := Std.HashSet.emptyWithCapacity 128
  closeAcc maxT cfg nfa ((insertAcc cfg (some (default, 0)) initial).1)

def checkConditions (cfg : Config) (M : Machine 4 1) (nfa : NFASet) (acc : AccSet) : Bool :=
  let h0 :=
    symbols.all fun i0 => nfaContains cfg nfa (none, i0, none)
  let h :=
    labels.all fun s0 =>
      cfg.uList.all fun u0 =>
        symbols.all fun i0 =>
          match M.get s0 i0 with
          | .halt => nfaContains cfg nfa (some (s0, u0), i0, none)
          | _ => true
  let r :=
    labels.all fun s0 =>
      cfg.uList.all fun u0 =>
        symbols.all fun i0 =>
          match M.get s0 i0 with
          | .next i1 .right s1 => nfaContains cfg nfa (some (s0, u0), i0, some (s1, cfg.step u0 i1))
          | _ => true
  let l :=
    labels.all fun s0 =>
      symbols.all fun i0 =>
        match M.get s0 i0 with
        | .next i1 .left s1 =>
            cfg.uList.all fun u1 =>
              symbols.all fun i2 =>
                (optionStates cfg).all fun su2 =>
                  (optionStates cfg).all fun su3 =>
                    if nfaContains cfg nfa (some (s1, u1), i2, su2) then
                      if nfaContains cfg nfa (su2, i1, su3) then
                        nfaContains cfg nfa (some (s0, cfg.step u1 i2), i0, su3)
                      else
                        true
                    else
                      true
        | _ => true
  let dfa0 := cfg.step 0 (0 : Symbol 1) == 0
  let acc0 := accContains cfg acc (some (default, 0))
  let accH := !(accContains cfg acc none)
  let accClosed :=
    (optionStates cfg).all fun su0 =>
      (optionStates cfg).all fun su1 =>
        if nfaContains cfg nfa (su0, (0 : Symbol 1), su1) then
          if accContains cfg acc su0 then accContains cfg acc su1 else true
        else
          true
  -- Soundness: every DFA transition stays within the state range `{0, …, states}`,
  -- so that the DFA state of any left tape is always a valid state in `uList`.
  let dfaClosed :=
    cfg.uList.all fun u0 =>
      symbols.all fun i0 =>
        decide (cfg.step u0 i0 < cfg.states + 1)
  h0 && h && r && l && dfa0 && acc0 && accH && accClosed && dfaClosed

def run (maxT : Nat) (cfg : Config) (M : Machine 4 1) : Bool :=
  let nfa := buildNFA maxT cfg M
  let acc := buildAcc maxT cfg nfa
  checkConditions cfg M nfa acc

/-! ### Correctness of the FAR decider

We show that whenever `run maxT cfg M = true`, the machine `M` does not halt from
the initial configuration.  The certificate describes a DFA reading the left part
of the tape and an NFA reading the right part.  We let

* `leftState L` be the DFA state reached after reading the left tape `L`
  (from far left towards the head), and
* `phi C = some (C.state, leftState C.left)` be the NFA state attached to a
  configuration `C`.

A configuration is *accepted* when the NFA, starting from `phi C` and reading the
right part of the tape `C.head, …`, can reach the rejecting sink `none`.  The set
of *non*-accepted configurations is a closed set containing the initial
configuration but no halting configuration, which proves non-halting.
-/

namespace Correctness

/-- DFA state reached by reading the left tape `L` from far left towards the head.
The hypothesis `h0` (the DFA fixes state `0` on the blank symbol) makes this
well-defined on the trailing-blank quotient. -/
def leftState (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0)
    (L : Turing.ListBlank (Symbol 1)) : U :=
  L.liftOn (fun l => l.foldr (fun a acc => cfg.step acc a) 0) (by
    have hrep : ∀ n : ℕ, (List.replicate n (default : Symbol 1)).foldr
        (fun a acc => cfg.step acc a) 0 = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [List.replicate_succ, List.foldr_cons, ih]
          exact h0
    rintro a b ⟨n, rfl⟩
    simp only [List.foldr_append, hrep])

@[simp] lemma leftState_mk (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0)
    (l : List (Symbol 1)) :
    leftState cfg h0 (Turing.ListBlank.mk l) = l.foldr (fun a acc => cfg.step acc a) 0 := rfl

lemma leftState_cons (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0)
    (a : Symbol 1) (L : Turing.ListBlank (Symbol 1)) :
    leftState cfg h0 (L.cons a) = cfg.step (leftState cfg h0 L) a := by
  induction L using Turing.ListBlank.induction_on with
  | _ l => simp [Turing.ListBlank.cons_mk]

lemma leftState_default (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0) :
    leftState cfg h0 (default : Turing.ListBlank (Symbol 1)) = 0 := rfl

lemma leftState_consHeadTail (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0)
    (L : Turing.ListBlank (Symbol 1)) :
    cfg.step (leftState cfg h0 L.tail) L.head = leftState cfg h0 L := by
  conv_rhs => rw [← Turing.ListBlank.cons_head_tail L]
  rw [leftState_cons]

lemma leftState_lt (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0)
    (hclosed : ∀ u, u < cfg.states + 1 → ∀ i, cfg.step u i < cfg.states + 1)
    (L : Turing.ListBlank (Symbol 1)) : leftState cfg h0 L < cfg.states + 1 := by
  induction L using Turing.ListBlank.induction_on with
  | _ l =>
    simp only [leftState_mk]
    induction l with
    | nil => exact Nat.succ_pos _
    | cons a t ih => rw [List.foldr_cons]; exact hclosed _ ih a

/-- A TM configuration of the relevant shape. -/
abbrev TMConfig := TM.Table.Config 4 1

/-- The NFA edge relation recorded by the certificate. -/
def Edge (cfg : Config) (nfa : NFASet) (su : OStU) (a : Symbol 1) (su' : OStU) : Prop :=
  nfaContains cfg nfa (su, a, su') = true

/-- NFA reachability while reading a finite list of symbols, with every visited
state required to be one of the `optionStates`. -/
inductive ReachL (cfg : Config) (nfa : NFASet) : List (Symbol 1) → OStU → OStU → Prop
  | nil {su} (h : su ∈ optionStates cfg) : ReachL cfg nfa [] su su
  | cons {a as su mid dst} (hsu : su ∈ optionStates cfg)
      (e : Edge cfg nfa su a mid) (r : ReachL cfg nfa as mid dst) :
      ReachL cfg nfa (a :: as) su dst

lemma ReachL.src_mem {cfg : Config} {nfa L su dst} (h : ReachL cfg nfa L su dst) :
    su ∈ optionStates cfg := by
  cases h with
  | nil hsu => exact hsu
  | cons hsu _ _ => exact hsu

lemma ReachL.dst_mem {cfg : Config} {nfa L su dst} (h : ReachL cfg nfa L su dst) :
    dst ∈ optionStates cfg := by
  induction h with
  | nil hsu => exact hsu
  | cons _ _ _ ih => exact ih

lemma ReachL.trans {cfg : Config} {nfa L1 su mid} (h1 : ReachL cfg nfa L1 su mid) :
    ∀ {L2 dst}, ReachL cfg nfa L2 mid dst → ReachL cfg nfa (L1 ++ L2) su dst := by
  induction h1 with
  | nil hsu => intro L2 dst h2; simpa using h2
  | cons hsu e _ ih => intro L2 dst h2; exact ReachL.cons hsu e (ih h2)

lemma ReachL.snoc {cfg : Config} {nfa L su dst a dst'} (h : ReachL cfg nfa L su dst)
    (e : Edge cfg nfa dst a dst') (hd : dst' ∈ optionStates cfg) :
    ReachL cfg nfa (L ++ [a]) su dst' :=
  h.trans (ReachL.cons h.dst_mem e (ReachL.nil hd))

lemma none_mem (cfg : Config) : (none : OStU) ∈ optionStates cfg := by
  simp [optionStates]

/-- The NFA state attached to a configuration. -/
def phi (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0) (C : TMConfig) : OStU :=
  some (C.state, leftState cfg h0 C.tape.left)

lemma phi_mem (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0)
    (hclosed : ∀ u, u < cfg.states + 1 → ∀ i, cfg.step u i < cfg.states + 1)
    (C : TMConfig) : phi cfg h0 C ∈ optionStates cfg := by
  have hu : leftState cfg h0 C.tape.left ∈ cfg.uList := by
    rw [Config.uList, List.mem_range]
    exact leftState_lt cfg h0 hclosed _
  simp only [phi, optionStates, List.mem_cons]
  right
  rw [List.mem_flatMap]
  exact ⟨C.state, List.mem_finRange _, by rw [List.mem_map]; exact ⟨_, hu, rfl⟩⟩

/-- A configuration is accepted when the NFA can reach the rejecting sink `none`
reading a finite prefix of the right part of the tape. -/
def accepts (cfg : Config) (h0 : cfg.step 0 (0 : Symbol 1) = 0) (nfa : NFASet)
    (C : TMConfig) : Prop :=
  ∃ n : ℕ, ReachL cfg nfa (C.tape.right₀.take n) (phi cfg h0 C) none

lemma take_succ (Lb : Turing.ListBlank (Symbol 1)) (n : ℕ) :
    Lb.take (n + 1) = Lb.take n ++ [Lb.nth n] := by
  induction n generalizing Lb with
  | zero => simp
  | succ n ih =>
      show Lb.head :: Lb.tail.take (n + 1) = (Lb.head :: Lb.tail.take n) ++ [Lb.nth (n + 1)]
      rw [ih Lb.tail, Turing.ListBlank.nth_succ, List.cons_append]

/-- Padding: reaching `none` over `take n` extends to `take (n + k)` using the
self-loops of the sink `none`. -/
lemma accepts_add {cfg : Config} {h0 : cfg.step 0 (0 : Symbol 1) = 0} {nfa : NFASet}
    (hloop : ∀ i, Edge cfg nfa none i none) {C : TMConfig} {n : ℕ} (k : ℕ)
    (h : ReachL cfg nfa (C.tape.right₀.take n) (phi cfg h0 C) none) :
    ReachL cfg nfa (C.tape.right₀.take (n + k)) (phi cfg h0 C) none := by
  induction k with
  | zero => exact h
  | succ k ih =>
      have hk : n + (k + 1) = (n + k) + 1 := rfl
      rw [hk, take_succ]
      exact ih.snoc (hloop _) (none_mem cfg)

/-- The abstract facts guaranteed by a successful `checkConditions` run. -/
structure Conds (cfg : Config) (M : Machine 4 1) (nfa : NFASet) (acc : AccSet) : Prop where
  h0 : ∀ i : Symbol 1, Edge cfg nfa none i none
  halt : ∀ (s0 : Label 4) (u0 : U) (i0 : Symbol 1), u0 ∈ cfg.uList →
    M.get s0 i0 = .halt → Edge cfg nfa (some (s0, u0)) i0 none
  right : ∀ (s0 : Label 4) (u0 : U) (i0 i1 : Symbol 1) (s1 : Label 4), u0 ∈ cfg.uList →
    M.get s0 i0 = .next i1 .right s1 →
    Edge cfg nfa (some (s0, u0)) i0 (some (s1, cfg.step u0 i1))
  left : ∀ (s0 : Label 4) (i0 i1 : Symbol 1) (s1 : Label 4),
    M.get s0 i0 = .next i1 .left s1 → ∀ (u1 : U), u1 ∈ cfg.uList → ∀ (i2 : Symbol 1)
    (su2 su3 : OStU), su2 ∈ optionStates cfg → su3 ∈ optionStates cfg →
    Edge cfg nfa (some (s1, u1)) i2 su2 → Edge cfg nfa su2 i1 su3 →
    Edge cfg nfa (some (s0, cfg.step u1 i2)) i0 su3
  dfa0 : cfg.step 0 (0 : Symbol 1) = 0
  acc0 : accContains cfg acc (some (default, 0)) = true
  accNone : accContains cfg acc none = false
  accClosed : ∀ (su0 su1 : OStU), su0 ∈ optionStates cfg → su1 ∈ optionStates cfg →
    Edge cfg nfa su0 (0 : Symbol 1) su1 → accContains cfg acc su0 = true →
    accContains cfg acc su1 = true
  dfaClosed : ∀ u, u < cfg.states + 1 → ∀ i, cfg.step u i < cfg.states + 1

lemma conds_of {cfg : Config} {M : Machine 4 1} {nfa : NFASet} {acc : AccSet}
    (hc : checkConditions cfg M nfa acc = true) : Conds cfg M nfa acc := by
  simp only [checkConditions, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh0, hh⟩, hr⟩, hl⟩, hdfa0⟩, hacc0⟩, haccH⟩, haccClosed⟩, hdfaClosed⟩ := hc
  refine
    { h0 := ?_, halt := ?_, right := ?_, left := ?_, dfa0 := ?_, acc0 := ?_,
      accNone := ?_, accClosed := ?_, dfaClosed := ?_ }
  · intro i
    exact (List.all_eq_true.mp hh0) i (by simp [symbols])
  · intro s0 u0 i0 hu heq
    have h1 := (List.all_eq_true.mp hh) s0 (by simp [labels])
    have h2 := (List.all_eq_true.mp h1) u0 hu
    have h3 := (List.all_eq_true.mp h2) i0 (by simp [symbols])
    rw [heq] at h3
    exact h3
  · intro s0 u0 i0 i1 s1 hu heq
    have h1 := (List.all_eq_true.mp hr) s0 (by simp [labels])
    have h2 := (List.all_eq_true.mp h1) u0 hu
    have h3 := (List.all_eq_true.mp h2) i0 (by simp [symbols])
    rw [heq] at h3
    exact h3
  · intro s0 i0 i1 s1 heq u1 hu i2 su2 su3 hsu2 hsu3 e1 e2
    have h1 := (List.all_eq_true.mp hl) s0 (by simp [labels])
    have h2 := (List.all_eq_true.mp h1) i0 (by simp [symbols])
    rw [heq] at h2
    have h3 := (List.all_eq_true.mp h2) u1 hu
    have h4 := (List.all_eq_true.mp h3) i2 (by simp [symbols])
    have h5 := (List.all_eq_true.mp h4) su2 hsu2
    have h6 := (List.all_eq_true.mp h5) su3 hsu3
    have e1' : nfaContains cfg nfa (some (s1, u1), i2, su2) = true := e1
    have e2' : nfaContains cfg nfa (su2, i1, su3) = true := e2
    rw [if_pos e1', if_pos e2'] at h6
    exact h6
  · simpa using hdfa0
  · exact hacc0
  · simpa using haccH
  · intro su0 su1 hsu0 hsu1 e hacc
    have h1 := (List.all_eq_true.mp haccClosed) su0 hsu0
    have h2 := (List.all_eq_true.mp h1) su1 hsu1
    have e' : nfaContains cfg nfa (su0, 0, su1) = true := e
    rw [if_pos e', if_pos hacc] at h2
    exact h2
  · intro u hu i
    have hu' : u ∈ cfg.uList := by rw [Config.uList, List.mem_range]; exact hu
    have h1 := (List.all_eq_true.mp hdfaClosed) u hu'
    have h2 := (List.all_eq_true.mp h1) i (by simp [symbols])
    exact of_decide_eq_true h2

lemma take_cons (a : Symbol 1) (L : Turing.ListBlank (Symbol 1)) (n : ℕ) :
    (L.cons a).take (n + 1) = a :: L.take n := by
  simp [Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]

/-- (2a) A halting configuration is accepted: the NFA reaches the sink `none`
after reading the single head symbol. -/
lemma accepts_of_halt {cfg : Config} {M : Machine 4 1} {nfa : NFASet} {acc : AccSet}
    (cd : Conds cfg M nfa acc) {C : TMConfig}
    (hhalt : M.get C.state C.tape.head = .halt) : accepts cfg cd.dfa0 nfa C := by
  have hu : leftState cfg cd.dfa0 C.tape.left ∈ cfg.uList := by
    rw [Config.uList, List.mem_range]; exact leftState_lt cfg cd.dfa0 cd.dfaClosed _
  have hlist : C.tape.right₀.take 1 = [C.tape.head] := by
    show (C.tape.right.cons C.tape.head).take 1 = [C.tape.head]
    rw [take_cons]; simp
  refine ⟨1, ?_⟩
  rw [hlist]
  refine ReachL.cons (phi_mem cfg cd.dfa0 cd.dfaClosed C) ?_ (ReachL.nil (none_mem cfg))
  exact cd.halt C.state (leftState cfg cd.dfa0 C.tape.left) C.tape.head hu hhalt

/-- (2b, right) Backward closure of acceptance under a right-moving step. -/
lemma accepts_step_right {cfg : Config} {M : Machine 4 1} {nfa : NFASet} {acc : AccSet}
    (cd : Conds cfg M nfa acc) {C C' : TMConfig} {w : Symbol 1}
    (hget : M.get C.state C.tape.head = .next w Turing.Dir.right C'.state)
    (htape : C'.tape = (C.tape.write w).move Turing.Dir.right)
    (h : accepts cfg cd.dfa0 nfa C') : accepts cfg cd.dfa0 nfa C := by
  obtain ⟨n, hr⟩ := h
  have hu : leftState cfg cd.dfa0 C.tape.left ∈ cfg.uList := by
    rw [Config.uList, List.mem_range]; exact leftState_lt cfg cd.dfa0 cd.dfaClosed _
  have hleft : C'.tape.left = C.tape.left.cons w := by rw [htape]; rfl
  have hphiC' : phi cfg cd.dfa0 C'
      = some (C'.state, cfg.step (leftState cfg cd.dfa0 C.tape.left) w) := by
    unfold phi; rw [hleft, leftState_cons]
  have hcons : C.tape.right₀ = C'.tape.right₀.cons C.tape.head := by
    apply Turing.ListBlank.ext
    intro i
    cases i with
    | zero => rw [Turing.ListBlank.cons_nth_zero, Turing.Tape.right₀_nth]; rfl
    | succ k =>
        rw [Turing.ListBlank.cons_nth_succ, Turing.Tape.right₀_nth, Turing.Tape.right₀_nth,
          htape, Turing.Tape.move_right_nth, Turing.Tape.write_nth_of_ne_zero _ _ (by omega)]
        norm_cast
  have hlist : C.tape.right₀.take (n + 1) = C.tape.head :: C'.tape.right₀.take n := by
    rw [hcons, take_cons]
  refine ⟨n + 1, ?_⟩
  rw [hlist]
  refine ReachL.cons (phi_mem cfg cd.dfa0 cd.dfaClosed C) ?_ hr
  rw [hphiC']
  exact cd.right C.state (leftState cfg cd.dfa0 C.tape.left) C.tape.head w C'.state hu hget

/-- (2b, left) Backward closure of acceptance under a left-moving step. -/
lemma accepts_step_left {cfg : Config} {M : Machine 4 1} {nfa : NFASet} {acc : AccSet}
    (cd : Conds cfg M nfa acc) {C C' : TMConfig} {w : Symbol 1}
    (hget : M.get C.state C.tape.head = .next w Turing.Dir.left C'.state)
    (htape : C'.tape = (C.tape.write w).move Turing.Dir.left)
    (h : accepts cfg cd.dfa0 nfa C') : accepts cfg cd.dfa0 nfa C := by
  obtain ⟨m, hr⟩ := h
  have hu1 : leftState cfg cd.dfa0 C.tape.left.tail ∈ cfg.uList := by
    rw [Config.uList, List.mem_range]; exact leftState_lt cfg cd.dfa0 cd.dfaClosed _
  have hC'head : C'.tape.head = C.tape.left.head := by rw [htape]; rfl
  have hC'right : C'.tape.right = C.tape.right.cons w := by rw [htape]; rfl
  have hleft' : C'.tape.left = C.tape.left.tail := by rw [htape]; rfl
  have hphiC' : phi cfg cd.dfa0 C'
      = some (C'.state, leftState cfg cd.dfa0 C.tape.left.tail) := by
    unfold phi; rw [hleft']
  have hC'r0 : C'.tape.right₀ = (C.tape.right.cons w).cons C.tape.left.head := by
    show C'.tape.right.cons C'.tape.head = (C.tape.right.cons w).cons C.tape.left.head
    rw [hC'head, hC'right]
  have hlist' : C'.tape.right₀.take (m + 2)
      = C.tape.left.head :: w :: C.tape.right.take m := by
    rw [hC'r0, take_cons, take_cons]
  have hlistC : C.tape.right₀.take (m + 1) = C.tape.head :: C.tape.right.take m := by
    show (C.tape.right.cons C.tape.head).take (m + 1) = C.tape.head :: C.tape.right.take m
    rw [take_cons]
  have hpad : ReachL cfg nfa (C'.tape.right₀.take (m + 2)) (phi cfg cd.dfa0 C') none :=
    accepts_add cd.h0 2 hr
  rw [hlist'] at hpad
  cases hpad with
  | cons hsu0 e1 r1 =>
      cases r1 with
      | cons hsu1 e2 r2 =>
          rw [hphiC'] at e1
          have key := cd.left C.state C.tape.head w C'.state hget
            (leftState cfg cd.dfa0 C.tape.left.tail) hu1 C.tape.left.head _ _ hsu1 r2.src_mem e1 e2
          rw [leftState_consHeadTail] at key
          refine ⟨m + 1, ?_⟩
          rw [hlistC]
          exact ReachL.cons (phi_mem cfg cd.dfa0 cd.dfaClosed C) key r2

lemma mem_take_eq_zero {Lb : Turing.ListBlank (Symbol 1)} (hz : ∀ i, Lb.nth i = 0) :
    ∀ (n : ℕ), ∀ x ∈ Lb.take n, x = (0 : Symbol 1) := by
  intro n
  induction n generalizing Lb with
  | zero => intro x hx; simp at hx
  | succ n ih =>
      intro x hx
      rw [show Lb.take (n + 1) = Lb.head :: Lb.tail.take n from rfl] at hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; have h0 := hz 0; rwa [Turing.ListBlank.nth_zero] at h0
      · refine ih (fun i => ?_) x h
        have := hz (i + 1)
        rwa [Turing.ListBlank.nth_succ] at this

/-- Reading only blanks keeps the run inside the accept set. -/
lemma reachL_zeros_acc {cfg : Config} {M : Machine 4 1} {nfa : NFASet} {acc : AccSet}
    (cd : Conds cfg M nfa acc) {L su dst} (h : ReachL cfg nfa L su dst) :
    (∀ x ∈ L, x = (0 : Symbol 1)) → accContains cfg acc su = true →
      accContains cfg acc dst = true := by
  induction h with
  | nil => intro _ hacc; exact hacc
  | cons hsu e r ih =>
      intro hL hacc
      have ha : _ = (0 : Symbol 1) := hL _ List.mem_cons_self
      have hmid := cd.accClosed _ _ hsu r.src_mem (ha ▸ e) hacc
      exact ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hmid

/-- (1) The initial configuration is not accepted. -/
lemma not_accepts_init {cfg : Config} {M : Machine 4 1} {nfa : NFASet} {acc : AccSet}
    (cd : Conds cfg M nfa acc) : ¬ accepts cfg cd.dfa0 nfa TM.Table.init := by
  rintro ⟨n, hr⟩
  have hz : ∀ i, (TM.Table.init : TMConfig).tape.right₀.nth i = (0 : Symbol 1) := by
    intro i
    show ((default : Turing.ListBlank (Symbol 1)).cons default).nth i = (0 : Symbol 1)
    cases i with
    | zero => rw [Turing.ListBlank.cons_nth_zero]; rfl
    | succ k => rw [Turing.ListBlank.cons_nth_succ, Turing.ListBlank.default_nth]; rfl
  have hzeros := mem_take_eq_zero hz n
  have hphi : phi cfg cd.dfa0 (TM.Table.init : TMConfig) = some (default, 0) := by
    unfold phi
    have h1 : (TM.Table.init : TMConfig).state = default := rfl
    have h2 : (TM.Table.init : TMConfig).tape.left = (default : Turing.ListBlank (Symbol 1)) := rfl
    rw [h1, h2, leftState_default]
  have hacc0 : accContains cfg acc (phi cfg cd.dfa0 TM.Table.init) = true := by
    rw [hphi]; exact cd.acc0
  have hfin := reachL_zeros_acc cd hr hzeros hacc0
  rw [cd.accNone] at hfin
  simp at hfin

/-- The set of non-accepted configurations is a closed set containing the initial
configuration, hence the machine does not halt. -/
theorem nonhalting_of_conds {cfg : Config} {M : Machine 4 1} {nfa : NFASet} {acc : AccSet}
    (cd : Conds cfg M nfa acc) : ¬ M.halts TM.Table.init := by
  suffices hcs : ClosedSet M (fun C => ¬ accepts cfg cd.dfa0 nfa C) TM.Table.init from
    hcs.nonHalting
  refine ⟨?_, ?_⟩
  · rintro ⟨A, hA⟩
    rcases hstep : M.step A with _ | B
    · rw [Machine.step.none] at hstep
      exact absurd (accepts_of_halt cd hstep) hA
    · refine ⟨⟨B, ?_⟩, Machine.Progress.single hstep⟩
      obtain ⟨w, dir, hget, htape⟩ := Machine.step.some_rev hstep
      intro hB
      cases dir with
      | right => exact hA (accepts_step_right (C := A) (C' := B) cd hget htape hB)
      | left => exact hA (accepts_step_left (C := A) (C' := B) cd hget htape hB)
  · exact ⟨⟨TM.Table.init, not_accepts_init cd⟩, Machine.EvStep.refl⟩

end Correctness

private theorem run_eq_true_nonHalting
    (maxT : Nat) (cfg : Config) (M : Machine 4 1)
    (h : run maxT cfg M = true) :
    ¬M.halts TM.Table.init := by
  have hc : checkConditions cfg M (buildNFA maxT cfg M)
      (buildAcc maxT cfg (buildNFA maxT cfg M)) = true := h
  exact Correctness.nonhalting_of_conds (Correctness.conds_of hc)

def decider (maxT : Nat) (cfg : Config) (M : Machine 4 1) : HaltM M Unit :=
  if h : run maxT cfg M = true then
    .loops_prf (run_eq_true_nonHalting maxT cfg M h)
  else
    .unknown ()

end Deciders.FAR
