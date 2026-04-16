import Busybeaver.TM.Model.Reachability

namespace TM.Wrappers.Ticking

open TM.Model

variable {M : Type _} [TM.Model M]

structure Machine (M : Type _) where
  base : M

def wrap (m : M) : Machine M := ⟨m⟩

instance : Coe M (Machine M) := ⟨wrap⟩

instance : BlankSymbol (WithBot (TM.Model.Symbol M)) := ⟨⊥⟩

abbrev WrappedConfig (M : Type _) [TM.Model M] :=
  TM.Generic.Config (TM.Model.State M) (WithBot (TM.Model.Symbol M))

instance : Inhabited (WrappedConfig M) := ⟨⟨initial, default⟩⟩

private def liftStmt :
    Nat × GStmt (TM.Model.State M) (TM.Model.Symbol M) →
      Nat × GStmt (TM.Model.State M) (WithBot (TM.Model.Symbol M))
  | (dn, GStmt.halt) => (dn, GStmt.halt)
  | (dn, GStmt.next sym dir state) => (dn, GStmt.next (sym : WithBot (TM.Model.Symbol M)) dir state)

def forgetConfig (C : WrappedConfig M) : TM.Model.Config M := {
  state := C.state
  tape := C.tape.map {
    f := WithBot.unbotD default
    map_pt' := rfl
  }
}

@[simp] lemma forgetConfig_state (C : WrappedConfig M) : (forgetConfig C).state = C.state := rfl

@[simp] lemma forgetConfig_head (C : WrappedConfig M) :
    (forgetConfig C).tape.head = WithBot.unbotD default C.tape.head := rfl

@[simp] lemma forgetConfig_default :
    forgetConfig (default : WrappedConfig M) = (default : TM.Model.Config M) := by
  rfl

instance : TM.Model (Machine M) where
  State := TM.Model.State M
  Symbol := WithBot (TM.Model.Symbol M)
  instDecEqState := inferInstance
  instDecEqSymbol := inferInstance
  instBlankSymbol := ⟨⊥⟩
  instInitialState := inferInstance
  stmt w C := liftStmt (TM.Model.stmt w.base (forgetConfig C))
  stmt_eq_of_state_head_eq w A B hstate hhead := by
    have hstmt :
        TM.Model.stmt w.base (forgetConfig A) = TM.Model.stmt w.base (forgetConfig B) := by
      apply TM.Model.stmt_eq_of_state_head_eq w.base
      · simpa using hstate
      · exact congrArg (WithBot.unbotD default) hhead
    simpa [liftStmt] using congrArg liftStmt hstmt
  step w C :=
    match TM.Model.stmt w.base (forgetConfig C) with
    | (dn, .halt) => ⟨dn, .halted C⟩
    | (dn, .next sym dir state) =>
        ⟨dn, .continue { state, tape := C.tape.write (sym : WithBot (TM.Model.Symbol M)) |>.move dir }⟩
  step_stmt w C := by
    cases hs : TM.Model.stmt w.base (forgetConfig C) with
    | mk dn stmt =>
        cases stmt <;> rfl
  step_zero_iff w C := by
    cases hs : TM.Model.stmt w.base (forgetConfig C) with
    | mk dn stmt =>
        cases stmt with
        | halt =>
            have hzero := TM.Model.step_zero_iff w.base (forgetConfig C)
            rw [TM.Model.step_stmt w.base (forgetConfig C), hs] at hzero
            simp at hzero
            simp [hzero]
        | next sym dir state =>
            have hzero := TM.Model.step_zero_iff w.base (forgetConfig C)
            rw [TM.Model.step_stmt w.base (forgetConfig C), hs] at hzero
            simp at hzero
            constructor
            · intro hdn
              exact False.elim (hzero hdn)
            · intro h
              cases h

@[simp] lemma stmt_wrap (m : M) (C : WrappedConfig M) :
    TM.Model.stmt (wrap m) C = liftStmt (TM.Model.stmt m (forgetConfig C)) := rfl

lemma lastState_forget {m : M} {C : WrappedConfig M} :
    TM.Model.LastState (wrap m) C → TM.Model.LastState m (forgetConfig C) := by
  intro h
  cases hs : TM.Model.stmt m (forgetConfig C) with
  | mk dn stmt =>
      cases stmt <;>
        simp [TM.Model.LastState, TM.Model.step_stmt, stmt_wrap, liftStmt, hs] at h ⊢

lemma lastState_lift {m : M} {C : WrappedConfig M} :
    TM.Model.LastState m (forgetConfig C) → TM.Model.LastState (wrap m) C := by
  intro h
  cases hs : TM.Model.stmt m (forgetConfig C) with
  | mk dn stmt =>
      cases stmt <;>
        simp [TM.Model.LastState, TM.Model.step_stmt, stmt_wrap, liftStmt, hs] at h ⊢

private lemma stepBase_forget {m : M} {A B : WrappedConfig M} {n : Nat} :
    TM.Model.StepBase (wrap m) n A B →
      TM.Model.StepBase m n (forgetConfig A) (forgetConfig B) := by
  intro h
  unfold TM.Model.StepBase at h ⊢
  rw [TM.Model.step_stmt (wrap m) A] at h
  rw [TM.Model.step_stmt m (forgetConfig A)]
  cases hs : TM.Model.stmt m (forgetConfig A) with
  | mk dn stmt =>
      cases stmt with
      | halt =>
          simp [stmt_wrap, liftStmt, hs] at h ⊢
      | next sym dir state =>
          have h' :
              dn = n ∧
                ({ state := state, tape := Turing.Tape.move dir (Turing.Tape.write (sym : WithBot (TM.Model.Symbol M)) A.tape) } : WrappedConfig M) =
                  B := by
            simpa [stmt_wrap, liftStmt, hs] using h
          rcases h' with ⟨rfl, hB⟩
          cases hB
          simp [forgetConfig, Turing.Tape.map_write, Turing.Tape.map_move]

private lemma step_lift {m : M} {A : WrappedConfig M} {B : TM.Model.Config M} :
    (forgetConfig A -[m]->' B) →
      ∃ B' : WrappedConfig M, (A -[(wrap m)]->' B') ∧ forgetConfig B' = B := by
  intro h
  unfold TM.Model.Step at h
  rw [TM.Model.step_stmt m (forgetConfig A)] at h
  cases hs : TM.Model.stmt m (forgetConfig A) with
  | mk dn stmt =>
      cases stmt with
      | halt =>
          simp [hs] at h
      | next sym dir state =>
          let B' : WrappedConfig M := {
            state := state
            tape := A.tape.write (sym : WithBot (TM.Model.Symbol M)) |>.move dir
          }
          refine ⟨B', ?_, ?_⟩
          · unfold TM.Model.Step
            rw [TM.Model.step_stmt (wrap m) A]
            simp [stmt_wrap, B', hs, liftStmt]
          · simp [hs] at h
            have hB :
                { state := state, tape := (forgetConfig A).tape.write sym |>.move dir } = B := by
              simpa [TM.Model.Step, hs] using h
            rw [← hB]
            simp [B', forgetConfig, Turing.Tape.map_write, Turing.Tape.map_move]

private lemma evstep_lift_aux {m : M} {A₀ B : TM.Model.Config M} :
    (A₀ -[m]->*' B) →
      ∀ {A : WrappedConfig M}, forgetConfig A = A₀ →
        ∃ B' : WrappedConfig M, (A -[(wrap m)]->*' B') ∧ forgetConfig B' = B := by
  intro h
  induction h with
  | refl =>
      intro A hA
      exact ⟨A, .refl, hA⟩
  | step hAB hBC IH =>
      intro A hA
      rcases step_lift (A := A) (by simpa [hA] using hAB) with ⟨B', hAB'', hforgetB⟩
      rcases IH hforgetB with ⟨C', hBC', hforgetC⟩
      exact ⟨C', .step hAB'' hBC', hforgetC⟩

lemma multistepBase_forget {m : M} {A C : WrappedConfig M} {n : Nat} :
    TM.Model.MultistepBase (wrap m) n A C →
      forgetConfig A -[m]{n}->>' forgetConfig C := by
  intro h
  refine TM.Model.MultistepBase.rec
    (motive := fun n A C _ => forgetConfig A -[m]{n}->>' forgetConfig C)
    (show ∀ {C : WrappedConfig M}, forgetConfig C -[m]{0}->>' forgetConfig C from fun {_} => .refl)
    (fun {_ _ _ _ _} hAB _ IH => .step (stepBase_forget hAB) IH)
    h

lemma halts_of_wrapped_halts {m : M} {n : Nat} {C : WrappedConfig M}
    (h : TM.Model.LastState (wrap m) C ∧
      (TM.Model.MultistepBase (wrap m) n (default : WrappedConfig M) C)) :
    TM.Model.LastState m (forgetConfig C) ∧
      ((default : TM.Model.Config M) -[m]{n}->>' forgetConfig C) := by
  exact ⟨lastState_forget h.1, multistepBase_forget h.2⟩

lemma wrapped_halts_of_halts {m : M} :
    TM.Model.halts m (default : TM.Model.Config M) →
      TM.Model.halts (wrap m) (default : WrappedConfig M) := by
  intro h
  rcases h with ⟨n, C, hLast, hSteps⟩
  have hEv : (default : TM.Model.Config M) -[m]->*' C := by
    exact TM.Model.Multistep.to_evstep hSteps
  rcases evstep_lift_aux (A := (default : WrappedConfig M)) hEv forgetConfig_default with
    ⟨C', hEv', hforgetC⟩
  obtain ⟨n', hSteps'⟩ := TM.Model.Machine.EvStep.to_multistep hEv'
  exact ⟨n', C', lastState_lift (by simpa [hforgetC] using hLast), hSteps'⟩

end TM.Wrappers.Ticking
