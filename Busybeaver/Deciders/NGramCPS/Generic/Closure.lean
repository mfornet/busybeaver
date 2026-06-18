import Busybeaver.Deciders.NGramCPS.Generic.Successor
import Busybeaver.Deciders.NGramCPS.Generic.SearchProof

/-!
Generic port of `NGramCPS.ClosedSetProof`'s closure lemmas, over `GConfig`/`gstep`.

This proves the two facts the projection layer needs from a successful generic search:
- the blank initial configuration lies in `Base`, and
- `Base` is closed under progressing `gstep` moves.
-/

open TM.Table

namespace NGramCPS.Generic

variable {l : ℕ} {α : Type _} [Inhabited α] [DecidableEq α] {tm : Transition l α}

/-- The blank initial configuration satisfies the final `Base` predicate. -/
lemma ginit_base_of_closedResult {left right bound : ℕ} {finalState : SearchState l α}
    (hSearch : runSearch tm bound (initialState left right) = .closed finalState) :
    Base left right finalState (ginit : GConfig l α) := by
  refine ⟨⟨{
        left := Array.replicate left default
        head := default
        state := default
        right := Array.replicate right default
      }, ?_, ?_, rfl, ?_, ?_⟩, ?_, ?_⟩
  · exact runSearch_closed_preserves_partialConfig_mem hSearch (by simp [initialState])
  · rfl
  · simp
  · simp
  · intro k
    rw [blank_leftWindowAt]
    exact runSearch_closed_preserves_leftNGram_mem hSearch (by simp [initialState])
  · intro k
    rw [blank_rightWindowAt]
    exact runSearch_closed_preserves_rightNGram_mem hSearch (by simp [initialState])

/-- A successful generic search makes `Base` closed under progressing `gstep` moves. -/
lemma base_progress_of_closedResult {left right bound : ℕ} {finalState : SearchState l α}
    (hnl : left ≠ 0) (hnr : right ≠ 0)
    (hSearch : runSearch tm bound (initialState left right) = .closed finalState) :
    ∀ A : { C // Base left right finalState C },
      ∃ B : { C // Base left right finalState C }, gstep tm A.1 = some B.1 := by
  have hfrontier : (initialState (l := l) (α := α) left right).frontier =
      (initialState (l := l) (α := α) left right).partialConfigs.toList := by
    simp [initialState]
  intro A
  rcases A.property with ⟨⟨pc, hpc, hmatch⟩, hleft, hright⟩
  obtain ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩ :=
    partialConfig_fixpoint_of_closedResult hfrontier hSearch hpc
  cases hstmt : tm A.1.state A.1.tape.head with
  | none =>
      have hstmt' : tm pc.state pc.head = none := by
        rw [MatchesPartial_state hmatch, MatchesPartial_head hmatch]
        exact hstmt
      simp [stepPartialConfig, hstmt'] at hstep
  | some v =>
      obtain ⟨writeSym, dir, nextState⟩ := v
      cases dir with
      | right =>
          obtain ⟨pc', hpc'mem, hpc'match⟩ :=
            rightStep_has_matching_partialConfig hnl hnr hmatch hright
              ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩ hstmt
          refine ⟨⟨{ state := nextState, tape := (A.1.tape.write writeSym).move .right },
            ⟨⟨pc', hpc'mem, hpc'match⟩, ?_, ?_⟩⟩, ?_⟩
          · exact allLeftWindowsIn_of_rightStep hnl hmatch hleft
              ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩ hstmt
          · exact allRightWindowsIn_of_rightStep hright hstmt
          · simp [gstep, hstmt]
      | left =>
          obtain ⟨pc', hpc'mem, hpc'match⟩ :=
            leftStep_has_matching_partialConfig hnl hnr hmatch hleft
              ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩ hstmt
          refine ⟨⟨{ state := nextState, tape := (A.1.tape.write writeSym).move .left },
            ⟨⟨pc', hpc'mem, hpc'match⟩, ?_, ?_⟩⟩, ?_⟩
          · exact allLeftWindowsIn_of_leftStep hleft hstmt
          · exact allRightWindowsIn_of_leftStep hnr hmatch hright
              ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩ hstmt
          · simp [gstep, hstmt]

end NGramCPS.Generic
