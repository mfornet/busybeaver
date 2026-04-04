import Busybeaver.Deciders.NGramCPS.Windows

open TM

namespace NGramCPS

/--
`insertIfNew` never removes an existing element. This is the basic monotonicity
fact reused by future search-state membership lemmas.
-/
lemma mem_insertIfNew_of_mem [DecidableEq α] {as : Array α} {a x : α} (hx : x ∈ as) :
    x ∈ insertIfNew as a := by
  unfold insertIfNew
  split <;> simp [hx]

lemma blank_left_mem_initial (cfg : NGramCPSConfig) :
    let st := initialState (l := l) (s := s) cfg
    Array.replicate cfg.n default ∈ st.leftNGrams := by
  simp [initialState]

lemma blank_right_mem_initial (cfg : NGramCPSConfig) :
    let st := initialState (l := l) (s := s) cfg
    Array.replicate cfg.n default ∈ st.rightNGrams := by
  simp [initialState]

lemma initial_partial_mem (cfg : NGramCPSConfig) :
    let st := initialState (l := l) (s := s) cfg
    {
      left := Array.replicate cfg.n default,
      head := default,
      state := default,
      right := Array.replicate cfg.n default
    } ∈ st.partialConfigs := by
  simp [initialState]

lemma initial_matches (cfg : NGramCPSConfig) :
    MatchesPartial cfg.n
      {
        left := Array.replicate cfg.n default,
        head := default,
        state := default,
        right := Array.replicate cfg.n default
      }
      (init : Config l s) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · simp
  · simp

lemma initial_base (cfg : NGramCPSConfig) :
    let st := initialState (l := l) (s := s) cfg
    Base cfg.n st (init : Config l s) := by
  intro st
  constructor
  · refine ⟨{
        left := Array.replicate cfg.n default,
        head := default,
        state := default,
        right := Array.replicate cfg.n default
      }, initial_partial_mem (l := l) (s := s) cfg, initial_matches (l := l) (s := s) cfg⟩
  constructor
  · intro k
    rw [blank_leftWindowAt]
    exact blank_left_mem_initial (l := l) (s := s) cfg
  · intro k
    rw [blank_rightWindowAt]
    exact blank_right_mem_initial (l := l) (s := s) cfg

end NGramCPS
