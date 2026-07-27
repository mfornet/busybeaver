import Busybeaver.TM.Table.Reachability

/-- `evsteps t₁, …, tₙ` applies consecutive single machine steps via
`Machine.EvStep.step` and closes the chain with `Machine.EvStep.refl`. -/
syntax "evsteps " term,+ : tactic
macro_rules
  | `(tactic| evsteps $t:term) =>
      `(tactic| exact TM.Table.Machine.EvStep.step $t TM.Table.Machine.EvStep.refl)
  | `(tactic| evsteps $t:term, $ts:term,*) =>
      `(tactic| refine TM.Table.Machine.EvStep.step $t ?_ <;> evsteps $ts,*)

/-- `evchain t₁, …, tₙ` applies consecutive single machine steps via
`Machine.EvStep.step`, leaving the remaining goal open. -/
syntax "evchain " term,+ : tactic
macro_rules
  | `(tactic| evchain $t:term) =>
      `(tactic| refine TM.Table.Machine.EvStep.step $t ?_)
  | `(tactic| evchain $t:term, $ts:term,*) =>
      `(tactic| refine TM.Table.Machine.EvStep.step $t ?_ <;> evchain $ts,*)
