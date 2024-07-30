import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.ClosedSet

/-
Loopers are machines going through the same configuration twice.

It is enough to find a looping state, and to show that the machine reaches this state to show that the
machine loops

Note that because of the HaltM monad, execution of the machine through
-/

open TM

def looperDec [Inhabited $ Label l] [Inhabited $ Symbol s] (bound: ℕ) (M: Machine l s): HaltM M Unit := Id.run do
  let rec looperDecInner (bound: ℕ) {ktort} (tort: {s // init -[M]{ktort}-> s}) {kheir} (heir: {s // init-[M]{kheir}-> s}) (hht: tort -[M]->* heir): HaltM M Unit := match bound with
    | 0 => .unknown ()
    | n + 1 => do
      let nheir: {s // init -[M]{kheir+2}-> s} ← M.stepH heir >>= M.stepH
      let ntort: {s // init -[M]{ktort+1}-> s} ← M.stepH tort
      if heq: nheir.val = ntort.val then
        HaltM.loops_prf (by {
          obtain ⟨nheir, hnheir⟩ := nheir
          obtain ⟨ntort, hntort⟩ := ntort
          obtain ⟨tort, htort⟩ := tort
          obtain ⟨heir, hheir⟩ := heir
          simp_all
          apply ClosedSet.nonHalting (p:=(· = ntort))
          constructor
          · intro ⟨A, hA⟩
            simp_all
            have hTortNTort := htort.split_add hntort
            have hHeirNHeir := hheir.split_add hnheir
            obtain ⟨nth, hnth⟩ := hht.to_multistep
            have htortNTort := calc tort
              _ -[M]{nth}-> heir := hnth
              _ -[M]{2}-> ntort := hHeirNHeir

            conv at htortNTort =>
              pattern nth + 2
              rw [← one_add_one_eq_two, ← add_assoc, add_comm]

            apply Machine.Progress.from_multistep
            exact Machine.Multistep.split_add hTortNTort htortNTort
          · exists ⟨ntort, refl _⟩
            simp
            exact hntort.to_evstep
        })
      else
        looperDecInner n ntort nheir (by {
          obtain ⟨nheir, hnheir⟩ := nheir
          obtain ⟨ntort, hntort⟩ := ntort
          obtain ⟨tort, htort⟩ := tort
          obtain ⟨heir, hheir⟩ := heir
          simp_all

          obtain ⟨nth, hnth⟩ := hht.to_multistep
          apply Machine.Multistep.to_evstep
          have hTortNTort := htort.split_add hntort
          have hHeirNHeir := hheir.split_add hnheir
          have TortNHeir := calc tort
            _ -[M]{nth}-> heir := hnth
            _ -[M]{2}-> nheir := hHeirNHeir
          apply Machine.Multistep.split_le TortNHeir hTortNTort
          simp
        })
  looperDecInner bound ⟨init, Machine.Multistep.refl⟩ ⟨init, Machine.Multistep.refl⟩ Machine.EvStep.refl
