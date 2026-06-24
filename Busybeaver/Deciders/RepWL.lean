import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability
import Busybeaver.TM.Table.ClosedSet

open TM.Table

structure RepWLConfig where
  len : ℕ
  threshold : ℕ
  maxT : ℕ
  bound : ℕ
deriving DecidableEq, Repr

namespace Deciders.RepWL

abbrev Word (s : ℕ) := List (Symbol s)

structure RepeatWord (s : ℕ) where
  w : Word s
  minCnt : ℕ
  isConst : Bool
deriving DecidableEq, Repr

structure ListES (l s : ℕ) where
  left : List (Symbol s)
  right : List (Symbol s)
  head : Symbol s
  state : Label l
deriving DecidableEq, Repr

structure RepWLES (l s : ℕ) where
  left : List (RepeatWord s)
  right : List (RepeatWord s)
  state : Label l
  sgn : Turing.Dir
deriving DecidableEq, Repr

def initial : RepWLES l s := {
  left := []
  right := []
  state := default
  sgn := .right
}

def allBlank (w : Word s) : Bool :=
  w.all (· == default)

def push (cfg : RepWLConfig) (wl : List (RepeatWord s)) (w0 : Word s) :
    List (RepeatWord s) :=
  match wl with
  | v :: wl0 =>
      if v.w = w0 then
        let cnt := v.minCnt + 1
        if cnt < cfg.threshold then
          { w := w0, minCnt := cnt, isConst := v.isConst } :: wl0
        else
          { w := w0, minCnt := cfg.threshold, isConst := false } :: wl0
      else
        { w := w0, minCnt := 1, isConst := true } :: wl
  | [] =>
      if allBlank w0 then
        []
      else
        [{ w := w0, minCnt := 1, isConst := true }]

def pop (cfg : RepWLConfig) (wl : List (RepeatWord s)) :
    Option (Word s × List (List (RepeatWord s))) :=
  match wl with
  | [] => some (List.replicate cfg.len default, [[]])
  | v :: wl0 =>
      match v.minCnt with
      | 0 => none
      | n + 1 =>
          let rest :=
            match n with
            | 0 => wl0
            | _ + 1 => { w := v.w, minCnt := n, isConst := true } :: wl0
          some (v.w, rest :: if v.isConst then [] else [wl])

def wordUpdateStep (M : Machine l s) (x : ListES l s) :
    Option (ListES l s × Option Turing.Dir) :=
  match M.get x.state x.head with
  | .halt => none
  | .next out .right nextState =>
      match x.right with
      | m1 :: r1 =>
          some ({ left := out :: x.left, right := r1, head := m1, state := nextState }, none)
      | [] =>
          some ({ left := x.left, right := [], head := out, state := nextState }, some .right)
  | .next out .left nextState =>
      match x.left with
      | m1 :: l1 =>
          some ({ left := l1, right := out :: x.right, head := m1, state := nextState }, none)
      | [] =>
          some ({ left := [], right := x.right, head := out, state := nextState }, some .left)

def wordUpdateSteps (M : Machine l s) : ListES l s → ℕ → Option (ListES l s × Turing.Dir)
  | _, 0 => none
  | x, n + 1 =>
      match wordUpdateStep M x with
      | some (x0, none) => wordUpdateSteps M x0 n
      | some (x0, some d) => some (x0, d)
      | none => none

def wordUpdate (cfg : RepWLConfig) (M : Machine l s)
    (state : Label l) (w0 : Word s) (sgn : Turing.Dir) :
    Option (Label l × Word s × Bool) :=
  match w0 with
  | [] => none
  | m0 :: w1 =>
      let start : ListES l s :=
        match sgn with
        | .right => { left := [], right := w1, head := m0, state }
        | .left => { left := w1, right := [], head := m0, state }
      match wordUpdateSteps M start cfg.maxT with
      | none => none
      | some (x1, d) =>
          match d with
          | .right => some (x1.state, x1.head :: x1.left, decide (sgn ≠ d))
          | .left => some (x1.state, x1.head :: x1.right, decide (sgn ≠ d))

def stepOne (cfg : RepWLConfig) (M : Machine l s)
    (x : RepWLES l s) (w0 : Word s) (r1 : List (RepeatWord s)) :
    Option (RepWLES l s) :=
  match wordUpdate cfg M x.state w0 x.sgn with
  | none => none
  | some (state1, w1, isBack) =>
      if isBack then
        some {
          left := push cfg r1 w1
          right := x.left
          state := state1
          sgn := x.sgn.other
        }
      else
        some {
          left := push cfg x.left w1
          right := r1
          state := state1
          sgn := x.sgn
        }

def stepAll (cfg : RepWLConfig) (M : Machine l s)
    (x : RepWLES l s) (w0 : Word s) :
    List (List (RepeatWord s)) → Option (List (RepWLES l s))
  | [] => some []
  | r1 :: rest =>
      match stepOne cfg M x w0 r1, stepAll cfg M x w0 rest with
      | some x1, some xs => some (x1 :: xs)
      | _, _ => none

def step (cfg : RepWLConfig) (M : Machine l s) (x : RepWLES l s) :
    Option (List (RepWLES l s)) :=
  match pop cfg x.right with
  | none => none
  | some (w0, branches) => stepAll cfg M x w0 branches

def insertNew [DecidableEq α] (queue : List α) (seen : Array α) (x : α) :
    List α × Array α :=
  if x ∈ seen then
    (queue, seen)
  else
    (x :: queue, seen.push x)

def insertAllNew [DecidableEq α] (queue : List α) (seen : Array α) :
    List α → List α × Array α
  | [] => (queue, seen)
  | x :: xs =>
      let (queue', seen') := insertNew queue seen x
      insertAllNew queue' seen' xs

def search (cfg : RepWLConfig) (M : Machine l s) : ℕ → List (RepWLES l s) →
    Array (RepWLES l s) → Bool
  | 0, queue, _ => queue.isEmpty
  | _ + 1, [], _ => true
  | n + 1, x :: queue, seen =>
      match step cfg M x with
      | none => false
      | some xs =>
          let (queue', seen') := insertAllNew queue seen xs
          search cfg M n queue' seen'

def run (cfg : RepWLConfig) (M : Machine l s) : Bool :=
  search cfg M cfg.bound [initial] #[initial]

/-! ### Correctness of the RepWL decider

The decider represents TM tapes as a list of repeated words (a regex of the form
`(00)^3+ (10)^2 A> (11) (00)^3+`).  Each abstract configuration `RepWLES` stands for a
*set* of concrete TM configurations (those whose tape matches the regex).  The `step`
function computes a finite list of successor abstractions such that every concrete
configuration matching `x` reaches, in one or more TM steps, a configuration matching one
of the successors.  The BFS `search` then looks for a closed set of abstractions; if it
finds one (and it contains the initial configuration but, being closed, cannot contain a
halting one) the machine does not halt.

This mirrors `Coq-BB5/CoqBB5/BB4/Deciders/Decider_RepWL.v`.
-/

namespace Correctness

/-- A `RepeatWord` `(w0)^min+` or `(w0)^min` matches a finite word (list of symbols). -/
inductive RepW_match : RepeatWord s → Word s → Prop
  | zero (w0 : Word s) : RepW_match ⟨w0, 0, true⟩ []
  | succ {w0 w1 : Word s} {n : ℕ} :
      RepW_match ⟨w0, n, true⟩ w1 → RepW_match ⟨w0, n + 1, true⟩ (w0 ++ w1)
  | nonconst {w0 w1 : Word s} {n n0 : ℕ} :
      n ≤ n0 → RepW_match ⟨w0, n0, true⟩ w1 → RepW_match ⟨w0, n, false⟩ w1

/-- A list of `RepeatWord`s matches a half-tape (the finite words concatenated, then
trailing blanks). -/
inductive RepWL_match : List (RepeatWord s) → Turing.ListBlank (Symbol s) → Prop
  | nil : RepWL_match [] default
  | cons {h : RepeatWord s} {t : List (RepeatWord s)} {fh : Word s}
      {ft : Turing.ListBlank (Symbol s)} :
      RepW_match h fh → RepWL_match t ft → RepWL_match (h :: t) (fh ++ ft)

/-- The abstract configuration `x` *represents* the concrete TM configuration `C`.

The `sgn` field records which way the head points: with `sgn = right` the right
word-list describes the inclusive right half-tape (head + everything to its right) and
the left word-list the left half-tape; with `sgn = left` the roles are mirrored. -/
def In_RepWL (x : RepWLES l s) (C : Config l s) : Prop :=
  C.state = x.state ∧
    ∃ lb rb : Turing.ListBlank (Symbol s),
      RepWL_match x.left lb ∧ RepWL_match x.right rb ∧
        (match x.sgn with
          | .right => C.tape.left = lb ∧ C.tape.right₀ = rb
          | .left => C.tape.right = lb ∧ C.tape.left₀ = rb)

/-- Prepending blanks to the all-blank half-tape gives the all-blank half-tape. -/
lemma replicate_append_default (n : ℕ) :
    (List.replicate n (default : Symbol s)) ++ (default : Turing.ListBlank (Symbol s))
      = default := by
  refine Turing.ListBlank.ext fun i => ?_
  rw [Turing.ListBlank.append_nth]
  split <;> simp [List.getElem_replicate]

/-- A word recognised by `allBlank` is a list of blanks. -/
lemma allBlank_eq_replicate {w : Word s} (h : allBlank w = true) :
    w = List.replicate w.length default := by
  induction w with
  | nil => rfl
  | cons a t ih =>
      simp only [allBlank, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨ha, ht⟩ := h
      have ih' := ih (by simpa [allBlank] using ht)
      rw [List.length_cons, List.replicate_succ]
      exact congrArg₂ List.cons ha ih'

/-- An all-blank word prepended to the all-blank half-tape is the all-blank half-tape. -/
lemma allBlank_append_default {w : Word s} (h : allBlank w = true) :
    w ++ (default : Turing.ListBlank (Symbol s)) = default := by
  conv_lhs => rw [allBlank_eq_replicate h]
  exact replicate_append_default _

/-! #### Inversion helpers for the match relations -/

lemma RepWL_match.cons_inv {v : RepeatWord s} {wl0 : List (RepeatWord s)}
    {f : Turing.ListBlank (Symbol s)} (hm : RepWL_match (v :: wl0) f) :
    ∃ fh ft, RepW_match v fh ∧ RepWL_match wl0 ft ∧ f = fh ++ ft := by
  cases hm with
  | cons hw hwl => exact ⟨_, _, hw, hwl, rfl⟩

lemma RepWL_match.nil_inv {f : Turing.ListBlank (Symbol s)}
    (hm : RepWL_match ([] : List (RepeatWord s)) f) : f = default := by
  cases hm; rfl

lemma RepW_match.succ_inv {w0 w : Word s} {n : ℕ}
    (hm : RepW_match ⟨w0, n + 1, true⟩ w) :
    ∃ w1, w = w0 ++ w1 ∧ RepW_match ⟨w0, n, true⟩ w1 := by
  cases hm with
  | succ h => exact ⟨_, rfl, h⟩

lemma RepW_match.zero_inv {w0 w : Word s} (hm : RepW_match ⟨w0, 0, true⟩ w) : w = [] := by
  cases hm; rfl

lemma RepW_match.nonconst_inv {w0 w : Word s} {n : ℕ}
    (hm : RepW_match ⟨w0, n, false⟩ w) :
    ∃ n0, n ≤ n0 ∧ RepW_match ⟨w0, n0, true⟩ w := by
  cases hm with
  | nonconst hle htrue => exact ⟨_, hle, htrue⟩

/-- `RepW_match ⟨w0, 1, true⟩ w0`: one copy of `w0`. -/
lemma RepW_match.one (w0 : Word s) : RepW_match ⟨w0, 1, true⟩ w0 := by
  have := RepW_match.succ (RepW_match.zero w0)
  simpa using this

/-! #### `push` and `pop` specifications -/

/-- Prepending `w0` to a half-tape matching `wl` yields one matching `push cfg wl w0`. -/
lemma push_spec (cfg : RepWLConfig) (wl : List (RepeatWord s)) (w0 : Word s)
    {f : Turing.ListBlank (Symbol s)} (hm : RepWL_match wl f) :
    RepWL_match (push cfg wl w0) (w0 ++ f) := by
  cases wl with
  | nil =>
      rw [hm.nil_inv]
      simp only [push]
      split
      · rename_i hb
        rw [allBlank_append_default hb]
        exact RepWL_match.nil
      · exact RepWL_match.cons (RepW_match.one w0) RepWL_match.nil
  | cons v wl0 =>
      obtain ⟨vw, vmc, visc⟩ := v
      obtain ⟨fh, ft, hw, hwl, rfl⟩ := hm.cons_inv
      simp only [push]
      split
      · -- `vw = w0`
        rename_i hvw
        subst hvw
        rw [← Turing.ListBlank.append_assoc']
        -- goal now matches `(vw ++ fh) ++ ft`
        split
        · -- `cnt < threshold`
          refine RepWL_match.cons ?_ hwl
          cases visc with
          | true => exact RepW_match.succ hw
          | false =>
              obtain ⟨n0, hle, htrue⟩ := hw.nonconst_inv
              exact RepW_match.nonconst (by omega) (RepW_match.succ htrue)
        · -- `cnt ≥ threshold`, new head is `⟨vw, threshold, false⟩`
          rename_i hge
          refine RepWL_match.cons ?_ hwl
          cases visc with
          | true =>
              exact RepW_match.nonconst (by omega) (RepW_match.succ hw)
          | false =>
              obtain ⟨n0, hle, htrue⟩ := hw.nonconst_inv
              exact RepW_match.nonconst (by omega) (RepW_match.succ htrue)
      · -- `vw ≠ w0`: fresh repeat word
        exact RepWL_match.cons (RepW_match.one w0)
          (RepWL_match.cons hw hwl)

/-- `pop` peels the first word `w` off any half-tape matching `wl`; the remainder
matches one of the branch lists. -/
lemma pop_spec (cfg : RepWLConfig) (wl : List (RepeatWord s)) {w : Word s}
    {ls : List (List (RepeatWord s))} (hpop : pop cfg wl = some (w, ls))
    {f : Turing.ListBlank (Symbol s)} (hm : RepWL_match wl f) :
    ∃ wl', wl' ∈ ls ∧ ∃ f1, RepWL_match wl' f1 ∧ f = w ++ f1 := by
  cases wl with
  | nil =>
      simp only [pop, Option.some.injEq, Prod.mk.injEq] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      rw [hm.nil_inv]
      refine ⟨[], List.mem_cons.2 (Or.inl rfl), default, RepWL_match.nil, ?_⟩
      exact (replicate_append_default cfg.len).symm
  | cons v wl0 =>
      obtain ⟨vw, vmc, visc⟩ := v
      obtain ⟨fh, ft, hw, hwl, rfl⟩ := hm.cons_inv
      cases vmc with
      | zero => simp [pop] at hpop
      | succ n =>
          simp only [pop, Option.some.injEq, Prod.mk.injEq] at hpop
          obtain ⟨rfl, rfl⟩ := hpop
          cases visc with
          | true =>
              -- `fh = vw ++ w1`, `RepW_match ⟨vw, n, true⟩ w1`
              obtain ⟨w1, rfl, hsub⟩ := hw.succ_inv
              refine ⟨_, List.mem_cons.2 (Or.inl rfl), w1 ++ ft, ?_, ?_⟩
              · cases n with
                | zero =>
                    rw [hsub.zero_inv]
                    simpa using hwl
                | succ m => exact RepWL_match.cons hsub hwl
              · exact Turing.ListBlank.append_assoc'
          | false =>
              obtain ⟨n0, hle, htrue⟩ := hw.nonconst_inv
              -- `n0 ≥ n + 1 > 0`
              obtain ⟨n0', rfl⟩ : ∃ n0', n0 = n0' + 1 := ⟨n0 - 1, by omega⟩
              obtain ⟨w1, rfl, hsub⟩ := htrue.succ_inv
              -- `RepW_match ⟨vw, n0', true⟩ w1`, with `n ≤ n0'`
              by_cases hcase : n0' = n
              · subst n0'
                refine ⟨_, List.mem_cons.2 (Or.inl rfl), w1 ++ ft, ?_, ?_⟩
                · cases n with
                  | zero =>
                      rw [hsub.zero_inv]
                      simpa using hwl
                  | succ m => exact RepWL_match.cons hsub hwl
                · exact Turing.ListBlank.append_assoc'
              · -- `n0' ≥ n + 1`: use the non-const branch `⟨vw, n+1, false⟩ :: wl0`
                refine ⟨⟨vw, n + 1, false⟩ :: wl0, by simp, w1 ++ ft, ?_, ?_⟩
                · exact RepWL_match.cons (RepW_match.nonconst (by omega) hsub) hwl
                · exact Turing.ListBlank.append_assoc'

/-! #### `wordUpdate` simulation soundness

A `ListES` `x` together with extension half-tapes `L`, `R` denotes the concrete config
`toConfig x L R`, whose tape is `⟨x.head, x.left ++ L, x.right ++ R⟩`.  When the head
exits the bounded part of the tape (after `wordUpdateSteps`), it lands in `L` or `R`; the
resulting config is described by `exitConfig`. -/

/-- The concrete configuration denoted by a `ListES` with the given half-tape extensions. -/
def toConfig (x : ListES l s) (L R : Turing.ListBlank (Symbol s)) : Config l s :=
  ⟨x.state, ⟨x.head, x.left ++ L, x.right ++ R⟩⟩

/-- The concrete configuration reached when the head exits the bounded region in
direction `d`. -/
def exitConfig (x1 : ListES l s) (d : Turing.Dir) (L R : Turing.ListBlank (Symbol s)) :
    Config l s :=
  match d with
  | .right => ⟨x1.state, ⟨R.head, (x1.head :: x1.left) ++ L, R.tail⟩⟩
  | .left => ⟨x1.state, ⟨L.head, L.tail, (x1.head :: x1.right) ++ R⟩⟩

/-- One bounded simulation step is a real TM step on the denoted configuration. -/
lemma wordUpdateStep_sound (M : Machine l s) (x : ListES l s)
    (L R : Turing.ListBlank (Symbol s)) :
    match wordUpdateStep M x with
    | none => True
    | some (x0, none) => toConfig x L R -[M]-> toConfig x0 L R
    | some (x0, some d) => toConfig x L R -[M]-> exitConfig x0 d L R := by
  obtain ⟨xl, xr, xh, xs⟩ := x
  cases hget : M.get xs xh with
  | halt => simp [wordUpdateStep, hget]
  | next out dir q' =>
      cases dir <;> [cases xl; cases xr] <;>
        simp only [wordUpdateStep, hget, toConfig, exitConfig] <;>
        simp [Machine.step, hget, Turing.Tape.write, Turing.Tape.move]

/-- A successful bounded simulation (`wordUpdateSteps`) corresponds to one or more real
TM steps ending at the exit configuration. -/
lemma wordUpdateSteps_sound (M : Machine l s) :
    ∀ (n : ℕ) (x x1 : ListES l s) (d : Turing.Dir),
      wordUpdateSteps M x n = some (x1, d) →
      ∀ L R, ∃ k, toConfig x L R -[M]{k + 1}-> exitConfig x1 d L R := by
  intro n
  induction n with
  | zero => intro x x1 d h; simp [wordUpdateSteps] at h
  | succ n IH =>
      intro x x1 d h L R
      rw [wordUpdateSteps] at h
      have hstep := wordUpdateStep_sound M x L R
      revert h hstep
      cases hwus : wordUpdateStep M x with
      | none => intro h _; simp at h
      | some p =>
          obtain ⟨x0, od⟩ := p
          cases od with
          | none =>
              intro h hstep
              simp only at h hstep
              obtain ⟨k, hk⟩ := IH x0 x1 d h L R
              exact ⟨k + 1, Machine.Multistep.succ hstep hk⟩
          | some d' =>
              intro h hstep
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨0, Machine.Multistep.single hstep⟩

/-- `wordUpdate` simulates the TM through the word `m0 :: w1'`, reaching the exit
configuration described by `exitConfig`.  The returned `isBack` records whether the head
exited the word going *backwards* (`sgn ≠ d`). -/
lemma wordUpdate_sound (cfg : RepWLConfig) (M : Machine l s) (st : Label l)
    (m0 : Symbol s) (w1' : Word s) (sgn : Turing.Dir)
    {st1 : Label l} {w1 : Word s} {isBack : Bool}
    (h : wordUpdate cfg M st (m0 :: w1') sgn = some (st1, w1, isBack))
    (L R : Turing.ListBlank (Symbol s)) :
    ∃ (x1 : ListES l s) (d : Turing.Dir) (k : ℕ),
      st1 = x1.state ∧
      w1 = (match d with | .right => x1.head :: x1.left | .left => x1.head :: x1.right) ∧
      isBack = decide (sgn ≠ d) ∧
      toConfig (match sgn with
                 | .right => ⟨[], w1', m0, st⟩
                 | .left => ⟨w1', [], m0, st⟩) L R -[M]{k + 1}-> exitConfig x1 d L R := by
  cases sgn with
  | right =>
      simp only [wordUpdate] at h
      cases hws : wordUpdateSteps M ⟨[], w1', m0, st⟩ cfg.maxT with
      | none => rw [hws] at h; simp at h
      | some p =>
          obtain ⟨x1, d⟩ := p
          rw [hws] at h
          obtain ⟨k, hk⟩ := wordUpdateSteps_sound M cfg.maxT _ x1 d hws L R
          cases d with
          | right =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨x1, .right, k, rfl, rfl, rfl, hk⟩
          | left =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨x1, .left, k, rfl, rfl, rfl, hk⟩
  | left =>
      simp only [wordUpdate] at h
      cases hws : wordUpdateSteps M ⟨w1', [], m0, st⟩ cfg.maxT with
      | none => rw [hws] at h; simp at h
      | some p =>
          obtain ⟨x1, d⟩ := p
          rw [hws] at h
          obtain ⟨k, hk⟩ := wordUpdateSteps_sound M cfg.maxT _ x1 d hws L R
          cases d with
          | right =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨x1, .right, k, rfl, rfl, rfl, hk⟩
          | left =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact ⟨x1, .left, k, rfl, rfl, rfl, hk⟩

/-! #### Progress for the abstract step -/

/-- `stepOne` soundness: every concrete configuration whose right region starts with the
popped word `w0` and continues matching `r1` reaches (in ≥ 1 steps) a configuration
matching the successor `x1out`. -/
lemma stepOne_spec (cfg : RepWLConfig) (M : Machine l s) (x : RepWLES l s) (w0 : Word s)
    (r1 : List (RepeatWord s)) {x1out : RepWLES l s}
    (h : stepOne cfg M x w0 r1 = some x1out) :
    ∀ C : Config l s,
      In_RepWL ⟨x.left, ⟨w0, 1, true⟩ :: r1, x.state, x.sgn⟩ C →
      ∃ C', (C -[M]->+ C') ∧ In_RepWL x1out C' := by
  obtain ⟨xleft, xright, xstate, xsgn⟩ := x
  cases w0 with
  | nil => simp [stepOne, wordUpdate] at h
  | cons m0 w1' =>
      simp only [stepOne] at h
      cases hwu : wordUpdate cfg M xstate (m0 :: w1') xsgn with
      | none => rw [hwu] at h; simp at h
      | some triple =>
          obtain ⟨st1, w1, isBack⟩ := triple
          rw [hwu] at h
          intro C hC
          obtain ⟨Cst, Chead, Cleft, Cright⟩ := C
          obtain ⟨hCstate, lb, rb, hlb, hrb, hshape⟩ := hC
          -- decompose `rb = (m0 :: w1') ++ ft` with `ft` matching `r1`
          obtain ⟨fh, ft, hfh, hr1, hrb_eq⟩ := hrb.cons_inv
          obtain ⟨wz, hfh_eq, hz⟩ := hfh.succ_inv
          rw [hz.zero_inv, List.append_nil] at hfh_eq
          rw [hfh_eq] at hrb_eq
          cases xsgn with
          | right =>
              -- head reads into the right region (`lb` = left half, `ft` = right rest)
              obtain ⟨x1, d, k, hst1, hw1, hisb, hstep⟩ :=
                wordUpdate_sound cfg M xstate m0 w1' .right hwu lb ft
              obtain ⟨hCleft, hCright0⟩ := hshape
              simp only [Turing.Tape.right₀] at hCright0
              rw [hrb_eq, Turing.ListBlank.append_cons, Turing.ListBlank.cons_injective] at hCright0
              obtain ⟨rfl, rfl⟩ := hCright0
              simp only [] at hCstate hCleft
              subst Cleft; subst Cst
              cases d with
              | right =>
                  have hbf : isBack = false := hisb.trans (by decide)
                  subst hbf
                  simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
                  subst x1out
                  refine ⟨exitConfig x1 .right lb ft,
                    Machine.Progress.from_multistep hstep, hst1.symm,
                    w1 ++ lb, ft, push_spec cfg xleft w1 hlb, hr1, ?_, ?_⟩
                  · simp only [exitConfig]; rw [hw1]
                  · simp only [exitConfig, Turing.Tape.right₀]
                    exact Turing.ListBlank.cons_head_tail ft
              | left =>
                  have hbt : isBack = true := hisb.trans (by decide)
                  subst hbt
                  simp only [reduceIte, Turing.Dir.other, Option.some.injEq] at h
                  subst x1out
                  refine ⟨exitConfig x1 .left lb ft,
                    Machine.Progress.from_multistep hstep, hst1.symm,
                    w1 ++ ft, lb, push_spec cfg r1 w1 hr1, hlb, ?_, ?_⟩
                  · simp only [exitConfig]; rw [hw1]
                  · simp only [exitConfig, Turing.Tape.left₀]
                    exact Turing.ListBlank.cons_head_tail lb
          | left =>
              -- head reads into the left region (mirror): `ft` = "far" side, `lb` = right region
              obtain ⟨x1, d, k, hst1, hw1, hisb, hstep⟩ :=
                wordUpdate_sound cfg M xstate m0 w1' .left hwu ft lb
              obtain ⟨hCright, hCleft0⟩ := hshape
              simp only [Turing.Tape.left₀] at hCleft0
              rw [hrb_eq, Turing.ListBlank.append_cons, Turing.ListBlank.cons_injective] at hCleft0
              obtain ⟨rfl, rfl⟩ := hCleft0
              simp only [] at hCstate hCright
              subst Cright; subst Cst
              cases d with
              | right =>
                  have hbt : isBack = true := hisb.trans (by decide)
                  subst hbt
                  simp only [reduceIte, Turing.Dir.other, Option.some.injEq] at h
                  subst x1out
                  refine ⟨exitConfig x1 .right ft lb,
                    Machine.Progress.from_multistep hstep, hst1.symm,
                    w1 ++ ft, lb, push_spec cfg r1 w1 hr1, hlb, ?_, ?_⟩
                  · simp only [exitConfig]; rw [hw1]
                  · simp only [exitConfig, Turing.Tape.right₀]
                    exact Turing.ListBlank.cons_head_tail lb
              | left =>
                  have hbf : isBack = false := hisb.trans (by decide)
                  subst hbf
                  simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
                  subst x1out
                  refine ⟨exitConfig x1 .left ft lb,
                    Machine.Progress.from_multistep hstep, hst1.symm,
                    w1 ++ lb, ft, push_spec cfg xleft w1 hlb, hr1, ?_, ?_⟩
                  · simp only [exitConfig]; rw [hw1]
                  · simp only [exitConfig, Turing.Tape.left₀]
                    exact Turing.ListBlank.cons_head_tail ft

/-- `stepAll` soundness: iterates `stepOne` over all `pop` branches. -/
lemma stepAll_spec (cfg : RepWLConfig) (M : Machine l s) (x : RepWLES l s) (w0 : Word s) :
    ∀ (branches : List (List (RepeatWord s))) {xs : List (RepWLES l s)},
      stepAll cfg M x w0 branches = some xs →
      ∀ (r1 : List (RepeatWord s)), r1 ∈ branches →
      ∀ C : Config l s, In_RepWL ⟨x.left, ⟨w0, 1, true⟩ :: r1, x.state, x.sgn⟩ C →
      ∃ C', (C -[M]->+ C') ∧ ∃ x1 ∈ xs, In_RepWL x1 C' := by
  intro branches
  induction branches with
  | nil => intro xs _ r1 hr1; simp at hr1
  | cons b rest IH =>
      intro xs h
      simp only [stepAll] at h
      cases hso : stepOne cfg M x w0 b with
      | none => rw [hso] at h; simp at h
      | some x1 =>
          cases hsa : stepAll cfg M x w0 rest with
          | none => rw [hso, hsa] at h; simp at h
          | some ys =>
              rw [hso, hsa] at h
              simp only [Option.some.injEq] at h
              subst h
              intro r1 hr1 C hC
              rcases List.mem_cons.mp hr1 with rfl | hr1'
              · obtain ⟨C', hCC', hIn⟩ := stepOne_spec cfg M x w0 r1 hso C hC
                exact ⟨C', hCC', x1, List.mem_cons.2 (Or.inl rfl), hIn⟩
              · obtain ⟨C', hCC', x2, hx2, hIn⟩ := IH hsa r1 hr1' C hC
                exact ⟨C', hCC', x2, List.mem_cons_of_mem _ hx2, hIn⟩

/-- `step` soundness (progress): every concrete configuration matching `x` reaches, in
one or more TM steps, a configuration matching one of the successors. -/
lemma step_spec (cfg : RepWLConfig) (M : Machine l s) (x : RepWLES l s)
    {xs : List (RepWLES l s)} (h : step cfg M x = some xs) :
    ∀ C : Config l s, In_RepWL x C →
      ∃ C', (C -[M]->+ C') ∧ ∃ x1 ∈ xs, In_RepWL x1 C' := by
  intro C hC
  simp only [step] at h
  cases hpop : pop cfg x.right with
  | none => rw [hpop] at h; simp at h
  | some pair =>
      obtain ⟨w0, branches⟩ := pair
      rw [hpop] at h
      obtain ⟨hCstate, lb, rb, hlb, hrb, hshape⟩ := hC
      obtain ⟨r1, hr1mem, f1, hf1, hrb_eq⟩ := pop_spec cfg x.right hpop hrb
      have hC' : In_RepWL ⟨x.left, ⟨w0, 1, true⟩ :: r1, x.state, x.sgn⟩ C := by
        refine ⟨hCstate, lb, w0 ++ f1, hlb, RepWL_match.cons (RepW_match.one w0) hf1, ?_⟩
        rw [← hrb_eq]; exact hshape
      exact stepAll_spec cfg M x w0 branches h r1 hr1mem C hC'

/-! #### Soundness of the BFS searcher

The `search` procedure maintains the invariant `SearchWF`: every configuration already
seen is either still in the queue or has all its successors in the seen set.  When the
queue empties, the seen set is *closed*, giving the closed-set certificate. -/

/-- Specification of `insertAllNew`: the resulting seen-set is `seen ∪ items`, and the
resulting queue contains the old queue plus every freshly-inserted item. -/
lemma insertAllNew_spec [DecidableEq α] (items : List α) :
    ∀ (queue : List α) (seen : Array α),
      (∀ z, z ∈ (insertAllNew queue seen items).2 ↔ (z ∈ seen ∨ z ∈ items)) ∧
      (∀ z, z ∈ queue ∨ (z ∈ items ∧ z ∉ seen) → z ∈ (insertAllNew queue seen items).1) := by
  induction items with
  | nil =>
      intro queue seen
      refine ⟨fun z => ?_, fun z hz => ?_⟩
      · simp [insertAllNew]
      · simpa [insertAllNew] using hz
  | cons a items IH =>
      intro queue seen
      by_cases ha : a ∈ seen
      · simp only [insertAllNew, insertNew, if_pos ha]
        obtain ⟨IH1, IH2⟩ := IH queue seen
        refine ⟨fun z => ?_, fun z hz => ?_⟩
        · rw [IH1 z]; aesop
        · exact IH2 z (by aesop)
      · simp only [insertAllNew, insertNew, if_neg ha]
        obtain ⟨IH1, IH2⟩ := IH (a :: queue) (seen.push a)
        refine ⟨fun z => ?_, fun z hz => ?_⟩
        · rw [IH1 z, Array.mem_push, List.mem_cons]; tauto
        · refine IH2 z ?_
          simp only [List.mem_cons, Array.mem_push] at hz ⊢
          tauto

/-- BFS search invariant: every seen configuration is still queued or already has all its
successors recorded. -/
def SearchWF (cfg : RepWLConfig) (M : Machine l s) (queue : List (RepWLES l s))
    (seen : Array (RepWLES l s)) : Prop :=
  ∀ z ∈ seen, z ∈ queue ∨ ∃ xs, step cfg M z = some xs ∧ ∀ y ∈ xs, y ∈ seen

/-- `insertAllNew` preserves the search invariant when expanding the head `x`. -/
lemma insertAllNew_preserves_WF (cfg : RepWLConfig) (M : Machine l s)
    (x : RepWLES l s) (queue0 : List (RepWLES l s)) (seen : Array (RepWLES l s))
    (xs : List (RepWLES l s)) (hstep : step cfg M x = some xs)
    (hwf : SearchWF cfg M (x :: queue0) seen) :
    SearchWF cfg M (insertAllNew queue0 seen xs).1 (insertAllNew queue0 seen xs).2 := by
  obtain ⟨hmem2, hmem1⟩ := insertAllNew_spec xs queue0 seen
  have hmono : ∀ z, z ∈ seen → z ∈ (insertAllNew queue0 seen xs).2 :=
    fun z hz => (hmem2 z).mpr (Or.inl hz)
  have hxs_sub : ∀ y ∈ xs, y ∈ (insertAllNew queue0 seen xs).2 :=
    fun y hy => (hmem2 y).mpr (Or.inr hy)
  have fromSeen : ∀ z, z ∈ seen → (z ∈ (insertAllNew queue0 seen xs).1 ∨
      ∃ ys, step cfg M z = some ys ∧ ∀ y ∈ ys, y ∈ (insertAllNew queue0 seen xs).2) := by
    intro z hzseen
    rcases hwf z hzseen with hq | hsucc
    · rcases List.mem_cons.mp hq with rfl | hq0
      · exact Or.inr ⟨xs, hstep, hxs_sub⟩
      · exact Or.inl (hmem1 z (Or.inl hq0))
    · obtain ⟨ys, hys, hys_seen⟩ := hsucc
      exact Or.inr ⟨ys, hys, fun y hy => hmono y (hys_seen y hy)⟩
  intro z hz
  rcases (hmem2 z).mp hz with hzseen | hzxs
  · exact fromSeen z hzseen
  · by_cases hzseen : z ∈ seen
    · exact fromSeen z hzseen
    · exact Or.inl (hmem1 z (Or.inr ⟨hzxs, hzseen⟩))

/-- If the search returns `true` it has built a closed seen-set containing the initial one. -/
lemma search_sound (cfg : RepWLConfig) (M : Machine l s) :
    ∀ (n : ℕ) (queue : List (RepWLES l s)) (seen : Array (RepWLES l s)),
      SearchWF cfg M queue seen → search cfg M n queue seen = true →
      ∃ seen' : Array (RepWLES l s), (∀ z ∈ seen, z ∈ seen') ∧
        ∀ z ∈ seen', ∃ xs, step cfg M z = some xs ∧ ∀ y ∈ xs, y ∈ seen' := by
  have closed_of_wf_nil : ∀ (seen : Array (RepWLES l s)), SearchWF cfg M [] seen →
      ∃ seen', (∀ z ∈ seen, z ∈ seen') ∧
        ∀ z ∈ seen', ∃ xs, step cfg M z = some xs ∧ ∀ y ∈ xs, y ∈ seen' :=
    fun seen hwf => ⟨seen, fun z hz => hz,
      fun z hz => (hwf z hz).resolve_left (by simp)⟩
  intro n
  induction n with
  | zero =>
      intro queue seen hwf hsearch
      cases queue with
      | nil => exact closed_of_wf_nil seen hwf
      | cons a t => simp [search] at hsearch
  | succ n IH =>
      intro queue seen hwf hsearch
      cases queue with
      | nil => exact closed_of_wf_nil seen hwf
      | cons x queue0 =>
          simp only [search] at hsearch
          cases hstep : step cfg M x with
          | none => rw [hstep] at hsearch; simp at hsearch
          | some xs =>
              rw [hstep] at hsearch
              have hwf' := insertAllNew_preserves_WF cfg M x queue0 seen xs hstep hwf
              obtain ⟨seen', hsub, hclosed⟩ :=
                IH (insertAllNew queue0 seen xs).1 (insertAllNew queue0 seen xs).2 hwf' hsearch
              refine ⟨seen', fun z hz => hsub _ ?_, hclosed⟩
              exact (insertAllNew_spec xs queue0 seen).1 z |>.mpr (Or.inl hz)

/-! #### Assembling the non-halting certificate -/

lemma cons_default_self :
    Turing.ListBlank.cons (default : Symbol s) default = default := by
  refine Turing.ListBlank.ext fun i => ?_
  cases i with
  | zero => simp only [Turing.ListBlank.cons_nth_zero, Turing.ListBlank.default_nth]
  | succ j => simp only [Turing.ListBlank.cons_nth_succ, Turing.ListBlank.default_nth]

/-- The initial abstract configuration represents the initial TM configuration. -/
lemma In_RepWL_initial : In_RepWL (initial : RepWLES l s) TM.Table.init := by
  refine ⟨rfl, default, default, RepWL_match.nil, RepWL_match.nil, rfl, ?_⟩
  exact cons_default_self

/-- Main soundness: a successful search yields a closed set of configurations containing
the initial one but no halting one, so the machine does not halt. -/
lemma nonhalting_of_search (cfg : RepWLConfig) (M : Machine l s)
    (h : search cfg M cfg.bound [initial] #[initial] = true) :
    ¬ M.halts TM.Table.init := by
  have hwf : SearchWF cfg M [initial] #[initial] := by
    intro z hz
    have hz' : z = initial := by simpa using hz
    exact Or.inl (by rw [hz']; exact List.mem_cons.2 (Or.inl rfl))
  obtain ⟨seen', hsub, hclosed⟩ := search_sound cfg M cfg.bound [initial] #[initial] hwf h
  have hinit_seen : initial ∈ seen' := hsub initial (by simp)
  suffices hcs : ClosedSet M (fun C => ∃ z ∈ seen', In_RepWL z C) TM.Table.init from
    hcs.nonHalting
  refine ⟨?_, ?_⟩
  · rintro ⟨A, z, hzseen, hzA⟩
    obtain ⟨ys, hys, hys_seen⟩ := hclosed z hzseen
    obtain ⟨A', hAA', x1, hx1, hInx1⟩ := step_spec cfg M z hys A hzA
    exact ⟨⟨A', x1, hys_seen x1 hx1, hInx1⟩, hAA'⟩
  · exact ⟨⟨TM.Table.init, initial, hinit_seen, In_RepWL_initial⟩, Machine.EvStep.refl⟩

end Correctness

private theorem run_eq_true_nonHalting
    (cfg : RepWLConfig) (M : Machine l s)
    (h : run cfg M = true) :
    ¬M.halts TM.Table.init :=
  Correctness.nonhalting_of_search cfg M h

def decider (cfg : RepWLConfig) (M : Machine l s) : HaltM M Unit :=
  if h : run cfg M = true then
    .loops_prf (run_eq_true_nonHalting cfg M h)
  else
    .unknown ()

end Deciders.RepWL
