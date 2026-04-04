import Busybeaver.Deciders.NGramCPS.SuccessorBaseLemmas

open TM

namespace NGramCPS

/--
In the right-moving case, the real machine successor stays inside the final
`Base` predicate.

Why this is correct:
- `MatchesPartial` identifies the visible window and state/head of the full
  configuration;
- the right-side window invariant supplies the actual far symbol needed to choose
  one successor from the stored `Expansion`;
- the fixpoint theorem guarantees that chosen successor partial configuration is
  already present in `finalState.partialConfigs`.

Proof outline:
- define the real one-step successor configuration;
- use the window invariants and the fixpoint witness to show it has a stored
  matching `PartialConfig`;
- show all its left/right side windows remain in the final `n`-gram sets.

Proof complexity:
- high; semantic, depending on tape-window transition lemmas and the algorithmic
  fixpoint theorem.
-/
lemma base_successor_of_rightStep_of_fixpoint (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {pc : PartialConfig l s} {writeSym : Symbol s} {nextState : Label l}
    (hcfg : cfg.n ≠ 0)
    (hmatch : MatchesPartial cfg.n pc A)
    (hleft : AllLeftWindowsIn cfg.n finalState.leftNGrams A)
    (hright : AllRightWindowsIn cfg.n finalState.rightNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : M.get A.state A.tape.head = .next writeSym .right nextState) :
    ∃ B : { C // Base cfg.n finalState C }, A -[M]->+ B := by
  let B : Config l s := {
    state := nextState
    tape := (A.tape.write writeSym).move .right
  }
  refine ⟨⟨B, ?_⟩, Machine.Progress.single ?_⟩
  · constructor
    · exact rightStep_has_matching_partialConfig (l := l) (s := s) (M := M) cfg
        hcfg hmatch hright hfix hstmt
    constructor
    · exact allLeftWindowsIn_of_rightStep (l := l) (s := s) (M := M) cfg
        hmatch hleft hfix hstmt
    · exact allRightWindowsIn_of_rightStep (l := l) (s := s) (M := M) cfg
        hright hstmt
  · exact Machine.step.some hstmt

/--
In the left-moving case, the real machine successor stays inside the final
`Base` predicate.

Why this is correct:
- this is the mirror image of the right-moving case;
- the left-side window invariant supplies the far symbol needed to choose the
  right stored successor from the `Expansion`.

Proof outline:
- define the real one-step successor configuration;
- reconstruct the stored successor partial configuration using the left-side
  window invariant and the fixpoint witness;
- propagate the left/right window coverage to the successor.

Proof complexity:
- high; semantic, symmetric to the right-moving theorem.
-/
lemma base_successor_of_leftStep_of_fixpoint (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {pc : PartialConfig l s} {writeSym : Symbol s} {nextState : Label l}
    (hcfg : cfg.n ≠ 0)
    (hmatch : MatchesPartial cfg.n pc A)
    (hleft : AllLeftWindowsIn cfg.n finalState.leftNGrams A)
    (hright : AllRightWindowsIn cfg.n finalState.rightNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : M.get A.state A.tape.head = .next writeSym .left nextState) :
    ∃ B : { C // Base cfg.n finalState C }, A -[M]->+ B := by
  let B : Config l s := {
    state := nextState
    tape := (A.tape.write writeSym).move .left
  }
  refine ⟨⟨B, ?_⟩, Machine.Progress.single ?_⟩
  · constructor
    · exact leftStep_has_matching_partialConfig (l := l) (s := s) (M := M) cfg
        hcfg hmatch hleft hfix hstmt
    constructor
    · exact allLeftWindowsIn_of_leftStep (l := l) (s := s) (M := M) cfg
        hleft hstmt
    · exact allRightWindowsIn_of_leftStep (l := l) (s := s) (M := M) cfg
        hmatch hright hfix hstmt
  · exact Machine.step.some hstmt

end NGramCPS
