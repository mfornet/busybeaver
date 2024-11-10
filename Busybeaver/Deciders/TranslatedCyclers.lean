/-
Translated cycler decider based on [transcripts](https://www.sligocki.com/2024/06/12/tm-transcripts.html).

The idea is to have a tape that records the fact that a machine is on one of the "trailing zeros" of
the tape. Using that we can define the "extended transcripts" used in the blog post.
-/
import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM

abbrev TickingTape s := Turing.Tape (WithBot (Symbol s))

structure TickingConfig (l s) where
  state : Label l
  tape : TickingTape s

instance TickingConfig.inhabited: Inhabited (TickingConfig l s) :=
  ⟨{state := default, tape := default}⟩

abbrev Tick (l s) := Label l × (WithBot (Symbol s))

section ToBase

/-
To convert a ticking tape to a normal tape, with use Turing.Tape.map with a "forgetting" operation.

We thus leverage the lemmas of Turing.Tape.move this way
-/

/- The "forgetting" pointed map -/
def unbot_pointed [Inhabited α]: Turing.PointedMap (WithBot α) α := {
  f := WithBot.unbot' default
  map_pt' := rfl
}

def TickingTape.forget (T: TickingTape s): Turing.Tape (Symbol s) :=
  T.map unbot_pointed

def TickingConfig.toConfig (C: TickingConfig l s): Config l s := {
  state := C.state,
  tape := C.tape.forget
}

instance TickingConfig.coeConfig: Coe (TickingConfig l s) (Config l s) := ⟨TickingConfig.toConfig⟩

variable {C: TickingConfig l s}

@[simp]
lemma TickingConfig.toConfig.state: C.toConfig.state = C.state := rfl

@[simp]
lemma TickingConfig.toConfig.head: C.toConfig.tape.head = WithBot.unbot' default C.tape.head := rfl

end ToBase

section PrettyPrint -- TODO: remove when decider is done
open Std.Format Lean

private def right_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => repr l.head :: (right_repr l.tail n)

private def left_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => left_repr l.tail n ++ [repr l.head]

instance: Repr (TickingConfig l s) := ⟨λ cfg _ ↦
  Std.Format.joinSep (left_repr cfg.tape.left 10) " " ++ s!" {cfg.state}>{repr cfg.tape.head} " ++ Std.Format.joinSep (right_repr cfg.tape.right 10) " "⟩

end PrettyPrint

def step_tick (M: Machine l s) (C: TickingConfig l s): Option (TickingConfig l s × Tick l s) :=
  match M C.state (WithBot.unbot' default C.tape.head)  with
  | .halt => .none
  | .next sym' dir lab' =>
    .some ({state := lab', tape := (C.tape.write ↑sym').move dir }, (C.state, C.tape.head))

namespace TReach

variable {M: Machine l s}

notation A " t-[" M ":" T "]-> " B => step_tick M A = Option.some (B, T)

/--
The transcript-building step relation.
-/
inductive MultiTStep (M: Machine l s): List (Tick l s) → TickingConfig l s → TickingConfig l s → Prop
| refl C : MultiTStep M [] C C
| step A B C t L : (A t-[M:t]-> B) → MultiTStep M L B C → MultiTStep M (t :: L) A C

notation A " t-[" M ":" L "]->> " B => MultiTStep M L A B

lemma single_step {A B: TickingConfig l s} (h: A t-[M : t]-> B): A -[M]-> B :=
by {
  simp [step_tick] at h
  split at h
  · simp_all
  rename_i heq
  simp at h
  obtain ⟨hB, _⟩ := h
  simp [Machine.step]
  split
  · rename_i heq'
    rw [heq] at heq'
    cases heq'
  rename_i heq'
  rw [heq] at heq'
  cases heq'
  simp
  rw [← hB]
  simp [TickingConfig.toConfig, TickingTape.forget, Turing.Tape.map_move]
  congr
}

@[simp]
lemma step_tick.none {M: Machine l s}: step_tick M C = .none ↔ M C.state (WithBot.unbot' default C.tape.head) = .halt :=
by {
  simp [step_tick]
  split <;> simp_all
}

lemma step_tick.state_deterministic (hAB: A t-[M:t]-> B) (hAB': A' t-[M:t]-> B'): A.state = A'.state ∧ B.state = B'.state :=
by {
  -- Little massage of the hypotheses
  simp [step_tick] at hAB
  split at hAB
  · cases hAB
  rename_i sym' dir lab' heq
  simp at hAB
  simp [← hAB.1]
  unfold step_tick at hAB'
  split at hAB'
  · cases hAB'
  simp at hAB'

  -- Now we begin the proof
  obtain ⟨hB', htA'⟩ := hAB'
  obtain ⟨hB, htA⟩ := hAB

  rw [← htA] at htA'
  simp at htA'
  obtain ⟨htA's, htA'h⟩ := htA'
  constructor
  · exact htA's.symm
  rename_i heq'
  simp [default] at heq'
  rw [htA's, htA'h, heq] at heq'
  cases heq'
  rw [← hB']
}

lemma MultiTStep.to_multistep (h: A t-[M : L]->> B): A -[M]{L.length}-> B :=
by induction h with
| refl => exact .refl
| step A B C t L hAB _ IH => exact Machine.Multistep.succ (single_step hAB) IH

@[simp]
lemma MultiTStep.single: (A t-[M:[t]]->> B) ↔ (A t-[M:t]-> B) :=
by {
  constructor
  · intro hAB
    cases hAB
    rename_i B' hAB' hBB'
    cases hBB'
    exact hAB'
  · intro hAB
    apply MultiTStep.step
    · exact hAB
    · exact MultiTStep.refl B
}

instance MultiTStep.trans: Trans (MultiTStep M L) (MultiTStep M L') (MultiTStep M (L ++ L')) :=
by {
  constructor
  intro A B C hAB hBC
  induction hAB with
  | refl A => simp [hBC]
  | step A B C' t L'' hAB _ IH => {
    specialize IH hBC
    simp
    apply MultiTStep.step A B C t (L'' ++ L') hAB IH
  }
}

lemma MultiTStep.split (h: A t-[M: L ++ L']->> B): ∃C, (A t-[M:L]->> C) ∧ C t-[M:L']->> B :=
by induction L generalizing A with
| nil => {
  use A
  simp at h
  constructor
  · exact .refl A
  · exact h
}
| cons head tail IH => {
  cases h
  rename_i C hAC hCB
  simp at hCB
  obtain ⟨C', hC'⟩ := IH hCB
  use C'
  constructor
  · exact MultiTStep.step A C C' head tail hAC hC'.1
  · exact hC'.2
}

/--
Induction principle that pops the tail of the transcript instead of the head.
-/
lemma MultiTStep.reverseInduction
  {motive: (L: List (Tick l s)) → (A B: TickingConfig l s) → (A t-[M:L]->> B) → Prop}
  (refl: (C: TickingConfig l s) → motive [] C C (.refl C))
  (tail:
    (A B C: TickingConfig l s) → (t: Tick l s) → (L: List (Tick l s)) →
    (hAB: A t-[M:L]->> B) → (hBC: B t-[M:t]-> C) → motive L A B hAB →
    motive (L ++ [t]) A C (by calc A
    _ t-[M:L]->> B := hAB
    _ t-[M:[t]]->> C := by {
      simp
      exact hBC
    }))
  (h: A t-[M:L]->> B): motive L A B h :=
by induction L using List.reverseRecOn generalizing B with
| nil => {
  cases h
  exact refl A
}
| append_singleton L t IH => {
  obtain ⟨C, hAC, hBC⟩ := h.split
  simp at hBC
  exact tail A C B t L hAC hBC (IH hAC)
}

lemma MultiTStep.state_deterministic (hAB: A t-[M:L]->> B) (hAB': A t-[M:L]->> B'): B.state = B'.state :=
by induction hAB using MultiTStep.reverseInduction generalizing B' with
| refl C => {
  cases hAB'
  rfl
}
| tail A C B t L _ hCB _ => {
  obtain ⟨C', _, hCB'⟩ := hAB'.split
  simp at hCB'
  obtain ⟨_, hBB'⟩ := step_tick.state_deterministic hCB hCB'
  exact hBB'
}

/-
The very convenient step-or-prove-termination function that greatly simplifies writing deciders that
step through an execution: if the machine stops at some point the decider also stops, proving
termination.
-/
def Machine.stepT
  (M: TM.Machine l s) (σ: {s // default t-[M : L]->> s}):
  HaltM M {s': (TickingConfig l s × Tick l s) // default t-[M : L ++ [s'.2]]->> s'.1} :=
  match hi: step_tick M σ.val with
  | .none => .halts_prf L.length σ.val (by {
    simp at hi
    constructor
    · simp [Machine.LastState]
      exact hi
    · exact σ.property.to_multistep
  })
  | .some (s, t) => .unknown ⟨(s, t), calc default
      _ t-[M:L]->> σ.val := σ.property
      _ t-[M:[t]]->> s := by {
        simp
        exact hi
      } ⟩

def List.repeat (L: List α): ℕ → List α
| 0 => []
| n + 1 => L ++ (List.repeat L n)

@[simp]
lemma List.repeat.zero: List.repeat L 0 = [] := rfl

@[simp]
lemma List.repeat.succ: List.repeat L (n + 1) = L ++ (List.repeat L n) := rfl

lemma List.repeat.concat_comm: List.repeat L n ++ L = L ++ List.repeat L n :=
by induction n with
| zero => simp
| succ n IH => simp [IH]

@[simp]
lemma List.repeat.length: (List.repeat L n).length = n * L.length :=
by induction n with
| zero => simp
| succ n IH => {
  simp
  rw [Nat.add_one_mul, IH, Nat.add_comm]
}

@[simp]
lemma List.repeat.add: List.repeat L (n + k) = List.repeat L n ++ List.repeat L k :=
by induction k with
| zero => simp
| succ k IH => {
  simp
  rw [← Nat.add_assoc, succ, ← concat_comm, IH]
  simp
  exact concat_comm
}

/--
If a ticking machine goes twice through the transcript, with a record within the transcript, then
we can push that cycle once more, keeping the same transcript

This is the key step in proving non-termination of translated cyclers.
-/
lemma ticking_extends (hAB: A t-[M: L]->> B) (hBC: B t-[M:L]->> C) (hRecord: (q, ⊥) ∈ L): ∃D, C t-[M:L]->> D :=
by {
  induction L generalizing A B C with
  | nil => simp at hRecord
  | cons head tail IH => {
    simp at hRecord
    rcases hRecord with hq | hq
    · cases hq
      sorry
    · sorry
  }
}

lemma ticking_extends_many (hAB: A t-[M: L]->> B) (hBC: B t-[M:L]->> C) (hRecord: (q, ⊥) ∈ L):
  ∃D, B t-[M:List.repeat L n]->> D :=
by induction n generalizing A B C with
| zero => {
  simp
  use B
  exact .refl B
}
| succ n IH => {
  simp
  obtain ⟨D, hCD⟩ := ticking_extends hAB hBC hRecord
  obtain ⟨E, hE⟩ := IH hBC hCD
  use E
  calc B
    _ t-[M:L]->> C := hBC
    _ t-[M:List.repeat L n]->> E := hE
}

/--
If a machine follows the transcript pattern of a translated cycler, then it loops.
-/
lemma ticking_loops (hAB: A t-[M: L]->> B) (hBC: B t-[M:L]->> C) (hRecord: (q, ⊥) ∈ L):
  ¬M.halts A :=
by {
  /- SKETCH

  Suppose the machine stops after n steps on configuration E. We thus have:

  A t-[M:L]->> B t-[M:L]->> C
  A ......................... -[M]{n}-> E

  Because of [ticking_extends_many], we can push past B as many times as we want, i.e:

  A t-[M:L]->> B t-[M:L]->> C ........... t-[M:List.repeat L k]->> E'
  A ......................... -[M]{n}-> E

  Thus it is actually possible to "step more" from E based on the ticking assumption, which
  contradicts it being a finishing state, concluding the proof.
  -/

  intro ⟨n, E, hEl, hEr⟩

  have hLlen: 0 < L.length := List.length_pos_of_mem hRecord

  have hLrep: n < (List.repeat L (n / L.length + 1)).length := by {
    simp
    rw [Nat.add_comm]
    exact Nat.lt_div_mul_add hLlen
  }

  obtain ⟨E', hE'⟩ := ticking_extends_many hAB hBC hRecord (n:= n / L.length)
  have hAE' := calc A
    _ t-[M:L]->> B := hAB
    _ t-[M:List.repeat L (n / L.length)]->> E' := hE'

  simp at hLrep

  have hAE'ms := hAE'.to_multistep
  simp at hAE'ms

  let nstep := L.length + n / L.length * L.length - n
  have hEE': E -[M]{nstep}-> E' := Machine.Multistep.split_le  hAE'ms hEr (Nat.le_of_lt hLrep)

  refine Machine.halts_in.no_multistep' hEl (C:=E') (n:=nstep) ?_ hEE'
  simp [nstep]
  exact Nat.zero_lt_sub_of_lt hLrep
}

lemma twice_loop (h: A t-[M:L ++ L]->> B) (hRecord: (q, ⊥) ∈ L): ¬(M.halts A) :=
by {
  obtain ⟨C, hAC, hCB⟩ := h.split
  exact ticking_loops hAC hCB hRecord
}

lemma twice_suffix_loop (h: A t-[M:L]->> B) (hL': L' ++ L' <:+ L) (hRecord: (q, ⊥) ∈ L'): ¬(M.halts A) :=
by {
  rw [List.suffix_iff_eq_append] at hL'
  rw [← hL'] at h

  obtain ⟨C, hAC, hCB⟩ := h.split
  have hCnothalts := twice_loop hCB hRecord
  have hAC' := hAC.to_multistep
  exact Machine.halts.skip hAC' hCnothalts
}

end TReach

lemma List.takeWhile_append_drop {p: α → Bool} (L: List α):
  (L.takeWhile p) ++ (L.drop (L.takeWhile p).length) = L :=
by induction L with
| nil => simp
| cons head tail IH => {
  by_cases h: p head = true
  · rw [List.takeWhile_cons_of_pos h]
    simp [IH]
  · rw [List.takeWhile_cons_of_neg h]
    simp
}

def detect_front_loop (q: Label l) (L: List (Tick l s)): Option { L': List (Tick l s) // L' ++ L' <+: ((q, ⊥) :: L) ∧ (q, ⊥) ∈ L' } :=
  let rec loopy (left: List (Tick l s)) (right: List (Tick l s))
    (hq: (q, ⊥) ∈ left) (hL: (q, ⊥) :: L = left ++ right):
      Option { P: List (Tick l s) × List (Tick l s) // (q, ⊥) :: L = P.1 ++ P.2 ∧ P.1 <+: P.2 ∧ (q, ⊥) ∈ P.1 } :=
    if hlr: left.length > right.length then
      .none -- This avoids searching too far
    else if hl: left <+: right then
      .some ⟨(left, right), ⟨hL, hl, hq⟩⟩
    else match right with
    | [] => by { -- Contradiction by the first if
      exfalso
      simp at hlr
      absurd hlr
      exact List.ne_nil_of_mem hq
    }
    | head :: tail =>
      let upto := tail.takeWhile (λ t ↦ t.2 ≠ ⊥)
      loopy (left ++ head :: upto) (tail.drop upto.length) (by {
      simp
      left
      exact hq
    }) (by {
      rw [hL]
      simp [upto]
      symm
      exact List.takeWhile_append_drop tail
    })
  termination_by right.length
  loopy [(q, ⊥)] L (by simp) (by simp) |>.map (λ ⟨(left, right), issum, ispref⟩ ↦ ⟨left, by {
    constructor
    · simp_all
      exact (List.prefix_append_right_inj left).mpr ispref.1
    · exact ispref.2
  }⟩)

abbrev TickCache (M: Machine l s) := { T: TickingConfig l s × List (Tick l s) // default t-[M:T.2.reverse]->> T.1}

@[specialize bound]
def translatedCyclerDecider (bound: ℕ) (M: Machine l s) (start: TickCache M := ⟨(default, []), by {
  simp
  exact TReach.MultiTStep.refl default
}⟩): HaltM M (TickCache M) :=
  let rec loop (n: ℕ) (history: List (Tick l s))
    (current: TickingConfig l s) (hC: default t-[M: history.reverse]->> current): HaltM M (TickCache M) :=
    match n with
    | .zero => .unknown ⟨(current, history), hC⟩
    | .succ n => do
      let ⟨(cfg, q, b), prf⟩ ← TReach.Machine.stepT M ⟨current, hC⟩
      let nh := (q, b) :: history
      have hprf : default t-[M:nh.reverse]->> cfg := by {
        simp at prf
        simp [nh]
        exact prf
      }
      if hb: b = ⊥ then
        match detect_front_loop q history with
        | some Lh => .loops_prf (by {
            obtain ⟨L, hL, hq⟩ := Lh
            have hL': L.reverse ++ L.reverse <:+ nh.reverse := by {
              conv_lhs =>
                rw [← List.reverse_append]
              rw [List.reverse_suffix]
              simp [nh, hb]
              exact hL
            }
            apply TReach.twice_suffix_loop hprf hL' (q:=q)
            simp
            exact hq
          })
        | none => loop n nh cfg hprf
      else
        loop n nh cfg hprf
  let ⟨(cfg, hist), prf⟩ := start
  loop bound hist cfg prf
