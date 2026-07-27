import Busybeaver.Deciders.Skelet.Skelet26
import Busybeaver.Enumerate.Perm
import Busybeaver.Enumerate.Symmetry
import Busybeaver.TM.Table.Parse

open TM.Table

namespace Deciders.Skelet.Skelet15
/-- Skelet #15's transition table. -/
abbrev M : Machine 4 1 := mach["1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC"]
/-!
### Non-halting proof for `M` (Skelet #15)

`1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC` is Skelet #15, which the Coq proof
(`BusyCoq/Skelet15.v`) closes by observing that it is Skelet #26 "with a different
initial state": mirroring the machine (`Machine.symm`, Coq `flip`) and relabelling
its states by the 5-cycle `A↦E, B↦C, C↦A, D↦B, E↦D` turns it into Skelet #26
(`sporadicMachine9`).  A relabelling is a composition of state swaps
(`Machine.perm`), each of which is halting-equivalent (`Machine.perm.equiv`), and
mirroring is halting-equivalent on the blank tape (`Machine.symm.equiv`).  The
composition maps the start state `A` to `E`, so the blank-tape run of Skelet #15
is halting-equivalent to Skelet #26 started in state `E`, which does not halt by
`Deciders.Skelet.Skelet26.nonHalting_E`. -/
theorem nonHalting : ¬ M.halts init := by
  have e0 : (M, (⟨(0 : Label 4), default⟩ : Config 4 1)) =H
            (M.symm, (⟨(0 : Label 4), default⟩ : Config 4 1)) :=
    Machine.symm.equiv
  have e1 : (M.symm, (⟨(0 : Label 4), default⟩ : Config 4 1)) =H
            (M.symm.perm 1 2,
              (⟨Machine.swap (1 : Label 4) 2 0, default⟩ : Config 4 1)) :=
    Machine.perm.equiv
  have e2 : (M.symm.perm 1 2,
              (⟨Machine.swap (1 : Label 4) 2 0, default⟩ : Config 4 1)) =H
            ((M.symm.perm 1 2).perm 3 1,
              (⟨Machine.swap (3 : Label 4) 1 (Machine.swap 1 2 0), default⟩ : Config 4 1)) :=
    Machine.perm.equiv
  have e3 : ((M.symm.perm 1 2).perm 3 1,
              (⟨Machine.swap (3 : Label 4) 1 (Machine.swap 1 2 0), default⟩ : Config 4 1)) =H
            (((M.symm.perm 1 2).perm 3 1).perm 4 3,
              (⟨Machine.swap (4 : Label 4) 3 (Machine.swap 3 1 (Machine.swap 1 2 0)), default⟩
                : Config 4 1)) :=
    Machine.perm.equiv
  have e4 : (((M.symm.perm 1 2).perm 3 1).perm 4 3,
              (⟨Machine.swap (4 : Label 4) 3 (Machine.swap 3 1 (Machine.swap 1 2 0)), default⟩
                : Config 4 1)) =H
            ((((M.symm.perm 1 2).perm 3 1).perm 4 3).perm 0 4,
              (⟨Machine.swap (0 : Label 4) 4 (Machine.swap 4 3 (Machine.swap 3 1 (Machine.swap 1 2 0))),
                  default⟩ : Config 4 1)) :=
    Machine.perm.equiv
  have hfin : ((((M.symm).perm 1 2).perm 3 1).perm 4 3).perm 0 4
      = Deciders.Skelet.Skelet26.M := by decide
  have hstate : Machine.swap (0 : Label 4) 4 (Machine.swap 4 3 (Machine.swap 3 1 (Machine.swap 1 2 0)))
      = (4 : Label 4) := by decide
  have E := ((((e0.trans e1).trans e2).trans e3).trans e4)
  rw [hfin, hstate] at E
  intro hhalt
  exact Deciders.Skelet.Skelet26.nonHalting_E (E.mp hhalt)


end Deciders.Skelet.Skelet15
