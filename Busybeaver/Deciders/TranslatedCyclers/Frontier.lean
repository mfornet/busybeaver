/-
Reachable frontier facts for ticking tapes.

This file captures the machine-specific invariant used by the translated cycler proof: for a
reachable ticking tape, once a cell on one side of the head is still `⊥`, every farther cell on
that side is also `⊥`.
-/
import Busybeaver.Deciders.TranslatedCyclers.Geometry

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

/-- Side-prefix invariant for reachable ticking tapes. -/
def SidePrefixes (T : Turing.Tape (TickSymbol BM)) : Prop :=
  ∃ l r : Nat,
    (∀ n : Nat, T.nth (Int.negSucc n) ≠ (⊥ : TickSymbol BM) ↔ n < l) ∧
    (∀ n : Nat, T.nth (Int.ofNat (n + 1)) ≠ (⊥ : TickSymbol BM) ↔ n < r)

/--
The default ticking tape has empty non-`⊥` prefixes on both sides.

Idea:
- unfold `Turing.Tape.nth` on the default tape and check both sides directly.
-/
lemma default_has_interval :
    SidePrefixes (BM := BM) (default : Turing.Tape (TickSymbol BM)) := by
  refine ⟨0, 0, ?_, ?_⟩
  · intro n
    constructor
    · intro h
      have h0 : (default : Turing.Tape (TickSymbol BM)).nth (Int.negSucc n) = (⊥ : TickSymbol BM) := by
        rfl
      exact False.elim (h h0)
    · intro h
      simp at h
  · intro n
    constructor
    · intro h
      have h0 : (default : Turing.Tape (TickSymbol BM)).nth (Int.ofNat (n + 1)) = (⊥ : TickSymbol BM) := by
        rfl
      exact False.elim (h h0)
    · intro h
      simp at h

/-- Writing a non-`⊥` symbol at the head preserves the side-prefix invariant. -/
lemma interval_after_write_nonbot {T : Turing.Tape (TickSymbol BM)} {sym : TickSymbol BM}
    (hT : SidePrefixes (BM := BM) T) (_hsym : sym ≠ (⊥ : TickSymbol BM)) :
    SidePrefixes (BM := BM) (T.write sym) := by
  rcases hT with ⟨l, r, hl, hr⟩
  refine ⟨l, r, ?_, ?_⟩
  · intro n
    rw [Turing.Tape.write_nth_of_ne_zero _ _ (by simp)]
    exact hl n
  · intro n
    rw [Turing.Tape.write_nth_of_ne_zero _ _ (by
      exact Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n))]
    exact hr n

/-- Moving left preserves the side-prefix invariant after a non-`⊥` head write. -/
lemma interval_after_move_left {T : Turing.Tape (TickSymbol BM)}
    (hT : SidePrefixes (BM := BM) T) (h0 : T.nth 0 ≠ (⊥ : TickSymbol BM)) :
    SidePrefixes (BM := BM) (T.move .left) := by
  rcases hT with ⟨l, r, hl, hr⟩
  refine ⟨l - 1, r + 1, ?_, ?_⟩
  · intro n
    rw [Turing.Tape.move_left_nth]
    have h' := hl (n + 1)
    constructor
    · intro h
      have : n + 1 < l := (h'.1 h)
      omega
    · intro h
      exact h'.2 (by omega)
  · intro n
    cases n with
    | zero =>
        rw [Turing.Tape.move_left_nth]
        simpa using h0
    | succ n =>
        rw [Turing.Tape.move_left_nth]
        simpa using hr n

/-- Moving right preserves the side-prefix invariant after a non-`⊥` head write. -/
lemma interval_after_move_right {T : Turing.Tape (TickSymbol BM)}
    (hT : SidePrefixes (BM := BM) T) (h0 : T.nth 0 ≠ (⊥ : TickSymbol BM)) :
    SidePrefixes (BM := BM) (T.move .right) := by
  rcases hT with ⟨l, r, hl, hr⟩
  refine ⟨l + 1, r - 1, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        rw [Turing.Tape.move_right_nth]
        simpa using h0
    | succ n =>
        rw [Turing.Tape.move_right_nth]
        simpa [Int.negSucc_eq] using hl n
  · intro n
    rw [Turing.Tape.move_right_nth]
    have h' := hr (n + 1)
    constructor
    · intro h
      have : n + 1 < r := (h'.1 h)
      omega
    · intro h
      exact h'.2 (by omega)

/-- A wrapped `next` statement never writes `⊥` (the ticking wrapper only writes real symbols). -/
lemma stmt_next_nonbot {m : TickingMachine BM} {A : TickingConfig BM}
    {dn : Nat} {sym : TickSymbol BM} {dir : Turing.Dir} {state : TM.Model.State BM}
    (h : TM.Model.stmt m A = (dn, GStmt.next sym dir state)) :
    sym ≠ (⊥ : TickSymbol BM) := by
  cases m with
  | mk base =>
      change TM.Model.stmt (TM.Wrappers.Ticking.wrap base) A = (dn, GStmt.next sym dir state) at h
      cases hbase : TM.Model.stmt base (TM.Wrappers.Ticking.forgetConfig A) with
      | mk dn' stmt =>
          cases stmt with
          | halt =>
              rw [TM.Wrappers.Ticking.stmt_wrap, hbase] at h
              cases h
          | next sym' dir' state' =>
              rw [TM.Wrappers.Ticking.stmt_wrap, hbase] at h
              injection h with _ hstmt
              injection hstmt with hsym _ _
              subst hsym
              intro hbot
              cases hbot

/- Every reachable ticking configuration satisfies the side-prefix invariant. -/
private lemma sidePrefixes_step {m : TickingMachine BM} {A B : TickingConfig BM} {n : Nat}
    (hA : SidePrefixes (BM := BM) A.tape)
    (hAB : TM.Model.StepBase m n A B) :
    SidePrefixes (BM := BM) B.tape := by
  unfold TM.Model.StepBase at hAB
  rw [TM.Model.step_stmt m A] at hAB
  cases hstmt : TM.Model.stmt m A with
  | mk dn stmt =>
      cases stmt with
      | halt =>
          simp [hstmt] at hAB
      | next sym dir state =>
          simp [hstmt] at hAB
          rcases hAB with ⟨rfl, hCfg⟩
          cases hCfg
          have hsym : sym ≠ (⊥ : TickSymbol BM) := stmt_next_nonbot hstmt
          have hwrite : SidePrefixes (BM := BM) (A.tape.write sym) :=
            interval_after_write_nonbot hA hsym
          have hhead : (A.tape.write sym).nth 0 ≠ (⊥ : TickSymbol BM) := by
            rw [Turing.Tape.write_nth_zero]; exact hsym
          cases dir with
          | left =>
              simpa using interval_after_move_left hwrite hhead
          | right =>
              simpa using interval_after_move_right hwrite hhead

/-- Every reachable ticking configuration satisfies the side-prefix invariant. -/
lemma reachable_nonbot_interval {m : TickingMachine BM} {A : TickingConfig BM} {n : Nat}
    (hA : (default : TickingConfig BM) -[m]{n}->>' A) :
    SidePrefixes (BM := BM) A.tape := by
  refine
    (TM.Model.MultistepBase.rec
      (motive := fun n A C _ => SidePrefixes (BM := BM) A.tape → SidePrefixes (BM := BM) C.tape)
      ?refl ?step hA) (default_has_interval (BM := BM))
  · intro C hC
    exact hC
  · intro A B C n₁ n₂ hAB hBC IH hA
    exact IH (sidePrefixes_step hA hAB)

/-- For reachable ticking tapes, a right-side `⊥` forces a whole right `⊥` suffix. -/
lemma reachable_bot_suffix_right {m : TickingMachine BM} {A : TickingConfig BM} {n : Nat}
    (hA : (default : TickingConfig BM) -[m]{n}->>' A)
    {k : Nat} (hbot : A.tape.nth (Int.ofNat (k + 1)) = (⊥ : TickSymbol BM)) :
    ∀ j : Nat, k ≤ j → A.tape.nth (Int.ofNat (j + 1)) = (⊥ : TickSymbol BM) := by
  rcases reachable_nonbot_interval (BM := BM) hA with ⟨l, r, hl, hr⟩
  have hk : ¬ k < r := by
    intro hk
    exact ((hr k).2 hk) hbot
  intro j hj
  by_cases hj' : A.tape.nth (Int.ofNat (j + 1)) ≠ (⊥ : TickSymbol BM)
  · have : j < r := (hr j).1 hj'
    omega
  · simpa using hj'

/-- For reachable ticking tapes, a left-side `⊥` forces a whole left `⊥` suffix. -/
lemma reachable_bot_suffix_left {m : TickingMachine BM} {A : TickingConfig BM} {n : Nat}
    (hA : (default : TickingConfig BM) -[m]{n}->>' A)
    {k : Nat} (hbot : A.tape.nth (Int.negSucc k) = (⊥ : TickSymbol BM)) :
    ∀ j : Nat, k ≤ j → A.tape.nth (Int.negSucc j) = (⊥ : TickSymbol BM) := by
  rcases reachable_nonbot_interval (BM := BM) hA with ⟨l, r, hl, hr⟩
  have hk : ¬ k < l := by
    intro hk
    exact ((hl k).2 hk) hbot
  intro j hj
  by_cases hj' : A.tape.nth (Int.negSucc j) ≠ (⊥ : TickSymbol BM)
  · have : j < l := (hl j).1 hj'
    omega
  · simpa using hj'

/-- `Int`-indexed right cascade: a `⊥` at a positive cell forces `⊥` everywhere further right. -/
lemma reachable_bot_mono_right {m : TickingMachine BM} {A : TickingConfig BM} {n : Nat}
    (hA : (default : TickingConfig BM) -[m]{n}->>' A)
    {a b : Int} (ha : 1 ≤ a) (hab : a ≤ b) (hbot : A.tape.nth a = (⊥ : TickSymbol BM)) :
    A.tape.nth b = (⊥ : TickSymbol BM) := by
  obtain ⟨ka, rfl⟩ : ∃ ka : Nat, a = Int.ofNat (ka + 1) :=
    ⟨(a - 1).toNat, by rw [Int.ofNat_eq_natCast]; omega⟩
  obtain ⟨kb, rfl⟩ : ∃ kb : Nat, b = Int.ofNat (kb + 1) :=
    ⟨(b - 1).toNat, by rw [Int.ofNat_eq_natCast]; omega⟩
  have hk : ka ≤ kb := by
    rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast] at hab
    omega
  exact reachable_bot_suffix_right hA hbot kb hk

/-- `Int`-indexed left cascade: a `⊥` at a negative cell forces `⊥` everywhere further left. -/
lemma reachable_bot_mono_left {m : TickingMachine BM} {A : TickingConfig BM} {n : Nat}
    (hA : (default : TickingConfig BM) -[m]{n}->>' A)
    {a b : Int} (ha : a ≤ -1) (hab : b ≤ a) (hbot : A.tape.nth a = (⊥ : TickSymbol BM)) :
    A.tape.nth b = (⊥ : TickSymbol BM) := by
  obtain ⟨ka, rfl⟩ : ∃ ka : Nat, a = Int.negSucc ka :=
    ⟨(-a - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
  obtain ⟨kb, rfl⟩ : ∃ kb : Nat, b = Int.negSucc kb :=
    ⟨(-b - 1).toNat, by rw [Int.negSucc_eq]; omega⟩
  have hk : ka ≤ kb := by
    rw [Int.negSucc_eq, Int.negSucc_eq] at hab
    omega
  exact reachable_bot_suffix_left hA hbot kb hk

/-- The write determined by a non-halting tick is never `⊥`. -/
lemma writeOfTick_ne_bot_of_next {m : TickingMachine BM} {t : Tick BM}
    {dn : Nat} {sym : TickSymbol BM} {dir : Turing.Dir} {st : TM.Model.State BM}
    (h : stmtOfTick m t = (dn, GStmt.next sym dir st)) :
    writeOfTick m t ≠ (⊥ : TickSymbol BM) := by
  have hsym : sym ≠ (⊥ : TickSymbol BM) :=
    stmt_next_nonbot (A := configOfTick t) h
  simp only [writeOfTick, h]
  exact hsym

end Deciders.TranslatedCyclers
