import Mathlib.Tactic
import Busybeaver.Basic
import Busybeaver.Reachability

variable {L S: ℕ} [Inhabited $ Label L] [Inhabited $ Symbol S]

open TM

lemma Machine.halts_of_no_halt {M: Machine L S} (h: ∀ (l: Label L) (s: Symbol S), M l s ≠ .halt):
  ¬M.halts := by {
    intro hM
    obtain ⟨⟨state, ⟨sym, _, _⟩⟩, ⟨hstf, _⟩⟩ := hM
    simp [Machine.LastState, Machine.step] at hstf
    split at hstf
    swap
    · cases hstf
    rename_i hstsy
    exact absurd hstsy (h state sym)
  }

instance {M: Machine L S}: Decidable (∀ (l: Label L) (s: Symbol S), M l s ≠ .halt) := inferInstance

def noHaltDec (M: Machine L S): HaltM M Unit :=
  if hm: (∀ l s, M l s ≠ .halt) then
    .loops_prf $ Machine.halts_of_no_halt hm
  else
    .unknown ()
