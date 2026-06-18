import Busybeaver.Deciders.NGramCPS.Generic.Closure
import Busybeaver.TM.Table.ClosedSet

/-!
Projection layer: turn a successful generic search (over an augmented alphabet `α`) into a
`ClosedSet` certificate for the real machine `M`, hence non-halting.

The augmented transition `tm` is assumed to *simulate* `M` along a pointed map `π : α → Symbol s`
(it reads only `π a` of an augmented symbol and writes a symbol projecting back to `M`'s write).
Under this assumption every augmented `gstep` projects onto a real `Machine.step`, so the
augmented `Base` closed set projects onto a real closed set containing the blank configuration.
-/

open TM.Table

namespace NGramCPS.Generic

variable {l s : ℕ} {α : Type _} [Inhabited α] [DecidableEq α]
  {tm : Transition l α} {M : Machine l s}

/-- `tm` simulates `M` along the pointed map `π`. -/
def Simulates (tm : Transition l α) (M : Machine l s)
    (π : Turing.PointedMap α (Symbol s)) : Prop :=
  ∀ (q : Label l) (a : α),
    match tm q a with
    | none => M.get q (π a) = Stmt.halt
    | some (w, d, ns) => M.get q (π a) = Stmt.next (π w) d ns

/-- Project an augmented configuration to a real configuration by forgetting decorations. -/
def projConfig (π : Turing.PointedMap α (Symbol s)) (C : GConfig l α) : Config l s :=
  { state := C.state, tape := C.tape.map π }

omit [DecidableEq α] in
/-- An augmented step projects onto a real machine step. -/
lemma gstep_some_projects {π : Turing.PointedMap α (Symbol s)} (hsim : Simulates tm M π)
    {C C' : GConfig l α} (h : gstep tm C = some C') :
    M.step (projConfig π C) = some (projConfig π C') := by
  rw [gstep] at h
  cases htm : tm C.state C.tape.head with
  | none =>
      rw [htm] at h
      simp at h
  | some v =>
      obtain ⟨w, d, ns⟩ := v
      rw [htm] at h
      simp only [Option.some.injEq] at h
      subst h
      have hsimqa := hsim C.state C.tape.head
      rw [htm] at hsimqa
      have hhead : (C.tape.map π).head = π C.tape.head := Turing.Tape.map_fst π C.tape
      have hstep : M.step (projConfig π C) =
          some ({ state := ns, tape := ((C.tape.map π).write (π w)).move d } : Config l s) := by
        have hs := Machine.step.some (M := M) (q := C.state) (T := C.tape.map π)
          (sym' := π w) (dir := d) (q' := ns) (by rw [hhead]; exact hsimqa)
        exact hs
      rw [hstep]
      simp [projConfig, Turing.Tape.map_move, Turing.Tape.map_write]

omit [DecidableEq α] in
/-- The blank augmented configuration projects to the blank real configuration. -/
lemma projConfig_ginit (π : Turing.PointedMap α (Symbol s)) :
    projConfig π (ginit : GConfig l α) = (init : Config l s) := by
  have hLB : (default : Turing.ListBlank α).map π = default := by
    show (Turing.ListBlank.mk []).map π = Turing.ListBlank.mk []
    rw [Turing.ListBlank.map_mk]
    simp
  have htape : (default : Turing.Tape α).map π = (default : Turing.Tape (Symbol s)) := by
    show Turing.Tape.map π ⟨default, default, default⟩ = ⟨default, default, default⟩
    simp only [Turing.Tape.map, Turing.PointedMap.map_pt, hLB]
  show (⟨default, (default : Turing.Tape α).map π⟩ : Config l s) = ⟨default, default⟩
  rw [htape]

/-- Main projection theorem: a successful generic search of a simulating transition proves the
real machine does not halt from the blank tape. -/
theorem nonHalting_of_closedResult {left right bound : ℕ} {finalState : SearchState l α}
    (π : Turing.PointedMap α (Symbol s)) (hsim : Simulates tm M π)
    (hnl : left ≠ 0) (hnr : right ≠ 0)
    (hSearch : runSearch tm bound (initialState left right) = .closed finalState) :
    ¬ M.halts (init : Config l s) := by
  have hbase := base_progress_of_closedResult (tm := tm) hnl hnr hSearch
  have hginit := ginit_base_of_closedResult (tm := tm) hSearch
  suffices hcs : ClosedSet M
      (fun C => ∃ Ĉ : GConfig l α, Base left right finalState Ĉ ∧ projConfig π Ĉ = C)
      (init : Config l s) from hcs.nonHalting
  refine ⟨?_, ?_⟩
  · rintro ⟨C, Ĉ, hC, hCeq⟩
    obtain ⟨B, hstepB⟩ := hbase ⟨Ĉ, hC⟩
    refine ⟨⟨projConfig π B.1, ⟨B.1, B.2, rfl⟩⟩, ?_⟩
    have hMstep : M.step (projConfig π Ĉ) = some (projConfig π B.1) :=
      gstep_some_projects hsim hstepB
    rw [hCeq] at hMstep
    exact Machine.Progress.single hMstep
  · exact ⟨⟨init, ginit, hginit, projConfig_ginit π⟩, Machine.EvStep.refl⟩

/-! ### Instances for the history- and LRU-augmented transitions -/

/-- The first projection of a `HistorySymbol`, as a pointed map. -/
def πfst : Turing.PointedMap (HistorySymbol l s) (Symbol s) := ⟨Prod.fst, rfl⟩

lemma historyTransition_simulates (history : ℕ) (M : Machine l s) :
    Simulates (historyTransition history M) M (πfst : Turing.PointedMap (HistorySymbol l s) (Symbol s)) := by
  intro q a
  unfold historyTransition
  cases h : M.get q a.fst with
  | halt => simp [h, πfst]
  | next ws dir nst => simp [h, πfst]

lemma lruTransition_simulates (M : Machine l s) :
    Simulates (lruTransition M) M (πfst : Turing.PointedMap (HistorySymbol l s) (Symbol s)) := by
  intro q a
  unfold lruTransition
  cases h : M.get q a.fst with
  | halt => simp [h, πfst]
  | next ws dir nst => simp [h, πfst]

end NGramCPS.Generic
