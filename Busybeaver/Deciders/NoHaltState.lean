import Busybeaver.Basic
import Busybeaver.Reachability

variable {L S: ℕ}

open TM

variable {M: Machine L S}

lemma Machine.halts_of_no_halt {M: Machine L S} (h: ∀ (l: Label L) (s: Symbol S), M l s ≠ .halt):
  ¬M.halts init := by {
    intro hM
    obtain ⟨n, ⟨state, ⟨head, _, _⟩ ⟩, finLast, _⟩ := hM
    simp [Machine.LastState, Machine.step] at finLast
    split at finLast
    swap
    · cases finLast
    rename_i hstsy
    exact absurd hstsy (h state head)
  }

lemma Machine.eq_zero_nonhalts (hM: M.n_halting_trans = 0): ¬M.halts default := by {
  simp [Machine.n_halting_trans, Machine.halting_trans, Finset.filter_eq_empty_iff] at hM
  exact Machine.halts_of_no_halt hM
}

instance {M: Machine L S}: Decidable (∀ (l: Label L) (s: Symbol S), M l s ≠ .halt) := inferInstance

def noHaltDec (M: Machine L S): HaltM M Unit :=
  if hm: (∀ l s, M l s ≠ .halt) then
    .loops_prf $ Machine.halts_of_no_halt hm
  else
    .unknown ()
