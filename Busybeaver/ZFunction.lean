--- Implement Z-Function
--- https://cp-algorithms.com/string/z-function.html
import Init.Data.Range
import Init.Data.Nat.Basic
import Init.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

namespace ZFunction

def longest (as : List α) (p : List α → Prop) : Prop :=
  p as ∧ ∀ x, p x → x.length ≤ as.length

lemma is_prefix_eq [BEq α] (as bs: List α) (hp : bs <+: as) (hb : i < bs.length) :
    as[i]'(hb.trans_le hp.length_le) = bs[i] := by
  exact Eq.symm (List.IsPrefix.getElem hp hb)

def slice (as : List α) (start size : ℕ) : List α :=
  (as.drop start).take size

def correct_z_function_value [BEq α] (as : List α) (i z : ℕ) : Prop :=
  i + z ≤ as.length ∧ longest (slice as i z) (fun x => x <+: as ∧ x <+: as.drop i)

structure PartialZArray [BEq α] (as : Array α) where
  table : Array ℕ
  is_z_function : (hb : i < table.data.length) →
    correct_z_function_value as.data i (table.get ⟨i, hb⟩)

def PartialZArray.init [BEq α] (as : Array α) : PartialZArray as :=
  let table := (Array.mkEmpty as.size).push as.size
  ⟨table, by
    rw [show table = #[as.size] from rfl]
    intro i b
    simp at b
    unfold correct_z_function_value
    simp [b]
    unfold slice
    constructor
    · simp
    · intro x hp
      simp
      exact List.IsPrefix.length_le hp
  ⟩

structure ZArray [BEq α] (as : Array α) where
  z_array : PartialZArray as
  complete : z_array.table.data.length = as.data.length

def ZArray.empty [BEq α] (as : Array α) (he : 0 = as.size): ZArray as :=
  ⟨⟨Array.mkEmpty as.size, by simp⟩, by simp; assumption⟩

structure LoopExtend [BEq α] (as : List α) (i : ℕ) where
  z : ℕ
  h : correct_z_function_value as i z

def loop_extend [BEq α] [DecidableEq α] (as: Array α) (i z : ℕ) (hp : (slice as.data i z) <+: as.data) (hb : i + z ≤ as.data.length): LoopExtend as.data i :=
    have hz : (slice as.data i z).length = z := by
      unfold slice
      simp
      exact Nat.le_sub_of_add_le' hb

    if b : i + z < as.size then
      have hm : min (z + 1) (as.data.length - i) = z + 1 := by
        simp
        exact Nat.le_sub_of_add_le' b

      have h_sz_len : as.size = as.data.length := by rfl

      if he : as[z]'(by linarith) = as[i + z] then
        loop_extend as i (z + 1) (by {
          let ⟨tail, hp'⟩ := hp
          use tail.drop 1
          apply List.ext_get
          · unfold slice
            simp
            symm
            apply (Nat.sub_eq_iff_eq_add _).mp
            · have h₁ := calc z + tail.length
                _ = (slice as.data i z).length + tail.length := by rw [hz]
                _ = (slice as.data i z ++ tail).length := List.length_append (slice as.data i z) tail |>.symm
                _ = as.data.length := congrArg List.length hp'

              calc as.size - (tail.length - 1)
                _ = z + tail.length - (tail.length - 1) := by rw [h_sz_len, ← h₁]
                _ = z + (tail.length - (tail.length - 1)) := Nat.add_sub_assoc (Nat.sub_le tail.length 1) z
                _ = z + (tail.length - tail.length + 1) := by
                    apply Nat.add_left_cancel_iff.mpr
                    rw [Nat.add_eq_right.mpr (Nat.sub_self tail.length)]
                    exact (Nat.sub_sub_self (by linarith))
                _ = z + 1 := by simp
                _ = min (z + 1) (as.size - i) := hm.symm
            · have h0 : (slice as.data i z ++ tail).length = as.data.length := congrArg List.length hp'
              have h1 : (slice as.data i z ++ tail).length = (slice as.data i z).length + tail.length := List.length_append (slice as.data i z) tail
              rw [h1] at h0
              apply Nat.sub_le_of_le_add
              apply Nat.le_add_right_of_le
              linarith
          · unfold slice
            simp
            intro n h₁ h₂
            by_cases hs : n ≤ z
            · have hi₁ : (List.take (z + 1) (List.drop i as.data)).length = z + 1 := by {
                simp
                exact Nat.le_sub_of_add_le' b
              }

              rw [
                show (List.take (z + 1) (List.drop i as.data) ++ tail.tail)[n]'(by {
                  simp
                  rw [hm]
                  exact Nat.lt_of_lt_of_eq h₁ (congrFun (congrArg HAdd.hAdd hm) (tail.length - 1))
                }) = (List.take (z + 1) (List.drop i as.data))[n] by apply List.getElem_append_left,

                show (List.take (z + 1) (List.drop i as.data))[n] = as.data[i + n] by {
                  rw [
                    show (List.take (z + 1) (List.drop i as.data))[n] = (List.drop i as.data)[n]'(by {
                      simp
                      calc n
                        _ ≤ z := hs
                        _ < as.data.length - i := Nat.lt_sub_iff_add_lt'.mpr b
                    }) by {
                      symm
                      apply List.getElem_take (List.drop i as.data) (by
                        simp
                        calc n
                          _ ≤ z := hs
                          _ ≤ (i + z) - i := le_add_tsub_swap
                          _ < as.data.length - i := Nat.sub_lt_sub_right (Nat.le_add_right i z) b) (by linarith)
                    }
                  ]
                  exact List.getElem_drop' as.data
                }
              ]

              by_cases h3 : n = z
              · cases h3
                exact he.symm
              · push_neg at h3
                have h4 : n < z := Nat.lt_of_le_of_ne hs h3
                have h5 : n < (slice as.data i z).length := by rw [hz]; exact h4
                rw [
                  show as.data[i + n] = (slice as.data i z)[n]'h5 by {
                    symm
                    unfold slice
                    have hi₂ := calc n
                        _ < z := h4
                        _ ≤ (i + z) - i := le_add_tsub_swap
                        _ < as.data.length - i := Nat.sub_lt_sub_right (Nat.le_add_right i z) b
                        _ = (as.data.drop i).length := by simp
                    rw [show (List.take z (List.drop i as.data))[n] = (List.drop i as.data)[n]
                      from List.getElem_take (as.data.drop i) hi₂ (by linarith) |>.symm]
                    exact List.getElem_drop' as.data
                  },

                  is_prefix_eq as.data (slice as.data i z) hp h5
                ]
            · have h₆ : z + tail.length = as.data.length := by {
                rw [← hz]
                nth_rewrite 2 [← hp']
                exact Eq.symm (List.length_append (slice as.data i z) tail)
              }

              have h₅ := calc n - (z + 1)
                  _ < as.size - (z + 1) := Nat.sub_lt_sub_right (by linarith[hs]) h₂
                  _ = as.data.length - (z + 1) := by simp
                  _ = z + tail.length - (z + 1) := by rw[← h₆]
                  _ = tail.length - 1 := Nat.add_sub_add_left z tail.length 1

              rw [
                show (List.take (z + 1) (List.drop i as.data) ++ tail.tail)[n]'(by simp; exact h₁) =
                  tail.tail[n - (List.take (z + 1) (List.drop i as.data)).length]'(by simp; rw[hm]; exact h₅) by {
                  apply List.getElem_append_right
                  simp
                  intro h
                  push_neg at hs
                  linarith
                }
              ]

              simp
              rw [
                show tail.tail[n - min (z + 1) (as.data.length - i)]'(by rw [hm, List.length_tail tail]; exact h₅) =
                    tail.tail[n - (z + 1)]'(by rw [List.length_tail tail]; exact h₅)
                  from getElem_congr (congrArg (HSub.hSub n) hm),

                show as.data[n] = (slice as.data i z ++ tail)[n]'(by simp; rw [hz, h₆]; exact h₂)
                  from List.getElem_of_eq hp'.symm h₂
              ]

              have hmw : n - (z + 1) < tail.tail.length := by rw [List.length_tail tail]; exact h₅

              rw [
                show tail.tail[n - (z + 1)]'hmw = tail[n - z] by {
                  rw [show tail[n - z] = tail[n - z - 1 + 1] from
                    getElem_congr ((Nat.sub_eq_iff_eq_add (tsub_pos_iff_not_le.mpr hs)).mp rfl)]
                  have hin : n - (z + 1) = n - z - 1 := by rfl
                  apply List.get_tail _ (n - z - 1) (by rw[List.length_tail tail, ←hin]; exact h₅) (by {
                    rw [← hin]
                    calc n - (z + 1) + 1
                      _ < tail.length - 1 + 1 := by linarith
                      _ = tail.length := Nat.sub_add_cancel (by linarith)
                  })
                },
                List.getElem_append_right (slice as.data i z) tail (by push_neg; rw [hz]; linarith)
              ]
              exact getElem_congr (congrArg (HSub.hSub n) (hz.symm))

        }) b
      else
        {
          z,
          h := by {
            constructor
            · exact hb
            · constructor
              · simp
                exact ⟨hp, List.take_prefix z (List.drop i as.data)⟩
              · intro x hp'
                rw [hz]
                contrapose! he
                let ls := List.drop i as.data
                calc as[z]
                  _ = x[z] := is_prefix_eq _ _ hp'.1 he
                  _ = ls[z]'(List.lt_length_drop as.data b) := is_prefix_eq ls x hp'.2 he |>.symm
                  _ = as[i + z] := List.getElem_drop' as.data
          }
        }
    else
      {
        z,
        h := by {
          constructor
          · exact hb
          · constructor
            · simp
              exact ⟨hp, List.take_prefix z (List.drop i as.data)⟩
            · intro x hp'
              apply List.IsPrefix.length_le
              push_neg at b
              apply List.prefix_take_iff.mpr
              exact ⟨hp'.2, calc x.length
                  _ ≤ (as.data.drop i).length := List.IsPrefix.length_le hp'.2
                  _ ≤ z := by simp; linarith⟩
        }
      }

def loop_build_table [BEq α] [DecidableEq α] (size i l r: ℕ) (zarray : PartialZArray as) (he : i = zarray.table.data.length) (hi : 0 < i) (hl : 0 < l) (hs : size + i = as.data.length) (hr : r ≤ as.data.length) (hg : l ≤ r) (hpre : slice as.data l (r - l) <+: as.data) (hlil : l ≤ i): ZArray (α := α) as :=
    match size with
    | 0 => ⟨zarray, by linarith[hs]⟩
    | n + 1 => (

      have hib := calc i - l
        _ < i := Nat.sub_lt hi hl
        _ = zarray.table.size := he

      let t := min (r - i) (zarray.table[i - l]'(hib))
      let z := if i < r then t else 0

      let ⟨z, hz⟩ := loop_extend as i z (by {
        by_cases hiz : i < r
        · have hzt : z = t := if_pos hiz
          rw [hzt]

          have ht : t ≤ r - i := Nat.min_le_left (r - i) zarray.table[i - l]
          have hlir : i ≤ r := Nat.le_of_succ_le hiz

          suffices slice as.data i t = as.data.take t by {
            rw [this]
            apply List.prefix_iff_eq_take.mpr
            simp
          }

          have h₃ : slice as.data l (r - l) = as.data.take (r - l) := by {
            rw [List.prefix_iff_eq_take.mp hpre]
            unfold slice
            simp
            have hl : r - l ≤ as.size - l := Nat.sub_le_sub_right hr l
            have hr : r - l ≤ as.size := calc r - l
              _ ≤ as.size - l := hl
              _ ≤ as.size := Nat.sub_le as.size l
            simp [hl, hr]
          }

          have h₄ : slice as.data (i - l) t = as.data.take t := by {
            have hb : i - l < zarray.table.data.length := by linarith
            have hl0 : t < as.size - (i - l) := calc t
              _ ≤ r - i := ht
              _ ≤ as.size - i := Nat.sub_le_sub_right hr i
              _ < as.size - i + l := Nat.lt_add_of_pos_right hl
              _ = as.size + l - i := Nat.sub_add_comm (Nat.le_trans hlir hr) |>.symm
              _ = as.size - (i - l) := Nat.Simproc.add_sub_le as.size hlil

            let hpre := (zarray.is_z_function hb).right.left.left
            simp at hpre

            have hpres : slice as.data (i - l) t <+: as.data := by {
              suffices slice as.data (i - l) t <+: slice as.data (i - l) zarray.table[i - l] from
                List.IsPrefix.trans this hpre
              unfold slice
              rw [List.prefix_take_le_iff (by simp; exact hl0)]
              exact Nat.min_le_right (r - i) zarray.table[i - l]
            }

            rw [List.prefix_iff_eq_take.mp hpres]
            unfold slice
            simp
            have hl : t ≤ as.size - (i - l) := Nat.le_of_succ_le hl0
            have hr : t ≤ as.size := calc t
              _ ≤ as.size - (i - l) := hl
              _ ≤ as.size := Nat.sub_le as.size (i - l)
            simp [hl, hr]
          }

          have hl : i - l + t ≤ r - l := calc i - l + t
            _ ≤ i - l + (r - i) := Nat.add_le_add_left ht (i - l)
            _ = i + (r - i) - l := Eq.symm (Nat.sub_add_comm hlil)
            _ = r - l := by aesop

          have h₅ : slice as.data i t = slice (slice as.data l (r - l)) (i - l) t := by {
            unfold slice
            nth_rewrite 2 [List.take_drop]
            rw [List.take_take, min_eq_left hl, List.drop_take]
            simp
            suffices i - l + l = i by (rw [this])
            exact Nat.sub_add_cancel hlil
          }

          have h₆ : slice (List.take (r - l) as.data) (i - l) t = slice as.data (i - l) t := by {
            unfold slice
            rw [List.take_drop, List.take_take, min_eq_left hl, List.drop_take]
            suffices i - l + t - (i - l) = t by (rw [this])
            simp
          }

          rw [h₅, h₃, h₆, h₄]
        · have hz0 : z = 0 := if_neg hiz
          rw [hz0]
          unfold slice
          simp
      }) (by {
            by_cases hiz : i < r
            · have hzt : z = t := if_pos hiz
              have hlt : t ≤ r - i := Nat.min_le_left (r - i) zarray.table[i - l]
              have htr : i ≤ r := Nat.le_of_succ_le hiz
              calc i + z
              _ = i + t := congrArg (HAdd.hAdd i) hzt
              _ ≤ i + (r - i) := by linarith[hlt]
              _ = r := Nat.add_sub_of_le htr
              _ ≤ as.data.length := hr
            · have hz0 : z = 0 := if_neg hiz
              simp [hz0]
              simp at hs
              linarith
          })
      let new_table := zarray.table.push z

      let new_zarray := ⟨new_table, by {
        intro j hb'
        by_cases h : j < zarray.table.data.length
        · rw [
            show new_table.get ⟨j, hb'⟩ = zarray.table.get ⟨j, h⟩ by apply Array.get_push_lt
          ]
          exact zarray.is_z_function h
        · simp
          rw [
            show new_table[j] = z by {
              rw [Array.get_push]
              simp
              intro h'
              contradiction
            },
            show j = i by {
              push_neg at h
              rw [he]
              rw [
                show new_table.data.length = zarray.table.data.length + 1 from Array.size_push zarray.table z
              ] at hb'
              linarith
            }
          ]
          exact hz
      }⟩

      if hnb : i + z > r then
        loop_build_table n (i + 1) i (i + z) (new_zarray) (by {
          rw [he]; simp;
          exact Eq.symm (Array.size_push zarray.table z)
        }) (by linarith) hi (by linarith) hz.left (by linarith) (by {
          suffices i + z - i = z by (rw[this]; exact hz.right.left.left)
          simp
        }) (by linarith)
      else
        loop_build_table n (i + 1) l r (new_zarray) (by {
          rw [he]; simp;
          exact Eq.symm (Array.size_push zarray.table z)
        }) (by linarith) hl (by linarith) hr hg hpre (by linarith)
    )

def z_function [BEq α] [DecidableEq α] (as : Array α) : ZArray as :=
  if he : 0 = as.size
    then ZArray.empty as he
  else
    loop_build_table (as.size - 1) 1 1 1 (PartialZArray.init as) rfl (by trivial) (by trivial) (Nat.succ_pred_eq_of_ne_zero fun a ↦ he a.symm) (Nat.one_le_iff_ne_zero.mpr fun a ↦ he a.symm) (by trivial) (by unfold slice; simp) (by trivial)

end ZFunction
