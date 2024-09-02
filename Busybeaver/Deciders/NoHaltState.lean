import Busybeaver.Basic
import Busybeaver.Reachability

variable {L S: ℕ}

open TM

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

instance {M: Machine L S}: Decidable (∀ (l: Label L) (s: Symbol S), M l s ≠ .halt) := inferInstance

def noHaltDec (M: Machine L S): HaltM M Unit :=
  if hm: (∀ l s, M l s ≠ .halt) then
    .loops_prf $ Machine.halts_of_no_halt hm
  else
    .unknown ()
