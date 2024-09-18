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
  let he : table = #[as.size] := rfl
  ⟨table, by
    rw [he]
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

lemma get_add_sub (l : List α) (h1 : 0 < a) (h2 : a < l.length) : l[a] = l[a - 1 + 1] := by
  refine getElem_congr ?h'
  exact (Nat.sub_eq_iff_eq_add h1).mp rfl

def loop_extend [BEq α] [DecidableEq α] (as: Array α) (i z : ℕ) (hp : (slice as.data i z) <+: as.data) (hb : i + z ≤ as.data.length): LoopExtend as.data i :=
    have hz : (slice as.data i z).length = z := by
      unfold slice
      simp
      exact Nat.le_sub_of_add_le' hb

    if b : i + z < as.size then
      have hm : min (z + 1) (as.data.length - i) = z + 1 := by
        simp
        exact Nat.le_sub_of_add_le' b

      have hbz : as.size = as.data.length := by simp

      if he : as[z]'(by linarith) = as[i + z] then
        loop_extend as i (z + 1) (by
          let ⟨tail, hp'⟩ := hp
          use tail.drop 1
          apply List.ext_get
          · unfold slice
            simp
            refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?_ ?_)
            · have h0 : (slice as.data i z ++ tail).length = as.data.length := congrArg List.length hp'
              have h1 : (slice as.data i z ++ tail).length = (slice as.data i z).length + tail.length := List.length_append (slice as.data i z) tail
              rw [h1] at h0
              refine Nat.sub_le_of_le_add ?_
              refine Nat.le_add_right_of_le ?_
              linarith
            · rw [hm]
              have h1 : (slice as.data i z ++ tail).length = as.data.length := congrArg List.length hp'
              have h2 : (slice as.data i z ++ tail).length = (slice as.data i z).length + tail.length := List.length_append (slice as.data i z) tail
              rw [h2] at h1
              rw [hz] at h1
              rw [hbz, ← h1]
              calc z + tail.length - (tail.length - 1) = z + (tail.length - (tail.length - 1)) := by (refine Nat.add_sub_assoc ?h z; exact Nat.sub_le tail.length 1)
                   _ = z + (tail.length - tail.length + 1) := by (
                    refine Eq.symm ((fun {m k n} ↦ Nat.add_left_cancel_iff.mpr) ?_)
                    simp
                    exact Eq.symm (Nat.sub_sub_self (by linarith)))
                   _ = z + 1 := by simp
          · unfold slice
            simp
            intro n h₁ h₂
            by_cases hs : n ≤ z
            · have h0 : (List.take (z + 1) (List.drop i as.data)).length = z + 1 := by
                simp
                exact Nat.le_sub_of_add_le' b
              have h1 : (List.take (z + 1) (List.drop i as.data) ++ tail.tail)[n]'(by
                simp
                rw [hm]
                exact Nat.lt_of_lt_of_eq h₁ (congrFun (congrArg HAdd.hAdd hm) (tail.length - 1))) = (List.take (z + 1) (List.drop i as.data))[n] := by
                  apply List.getElem_append_left

              rw [h1]
              have h2 : (List.take (z + 1) (List.drop i as.data))[n] = as.data[i + n] := by
                -- apply List.getElem_take
                have h2a : (List.drop i as.data)[n]'(by
                  simp
                  calc n ≤ z := hs
                       _ < as.data.length - i := Nat.lt_sub_iff_add_lt'.mpr b) = (List.take (z + 1) (List.drop i as.data))[n] := by
                  have hib : n < (List.drop i as.data).length := by
                    simp
                    calc n ≤ z := hs
                         _ ≤ (i + z) - i := le_add_tsub_swap
                         _ < as.data.length - i := by (
                          refine Nat.sub_lt_sub_right ?_ b
                          exact Nat.le_add_right i z)

                  apply List.getElem_take (List.drop i as.data) hib (by linarith)

                rw [← h2a]
                exact List.getElem_drop' as.data
              rw [h2]

              by_cases h3 : n = z
              · have h4 : as.data[z] = as.data[n] := getElem_congr h3.symm
                have h5 : as.data[i + z] = as.data[i + n] := getElem_congr (congrArg (HAdd.hAdd i) h3.symm)
                rw [← h4, ← h5]
                exact he.symm
              · push_neg at h3
                have h4 : n < z := Nat.lt_of_le_of_ne hs h3
                have h5 : n < (slice as.data i z).length := by
                  rw [hz]
                  exact h4
                have h6 : (slice as.data i z)[n]'h5 = as.data[i + n]  := by
                  unfold slice
                  have hnt : (List.drop i as.data)[n]'(by
                    simp
                    calc n < z := h4
                         _ ≤ (i + z) - i := le_add_tsub_swap
                         _ < as.data.length - i := by (
                          refine Nat.sub_lt_sub_right ?_ b
                          exact Nat.le_add_right i z
                        )
                    ) = (List.take z (List.drop i as.data))[n] := by
                    apply List.getElem_take (as.data.drop i) (by
                      simp
                      calc n < z := h4
                          _ ≤ (i + z) - i := by exact le_add_tsub_swap
                           _ < as.data.length - i := by (
                            refine Nat.sub_lt_sub_right ?_ b
                            exact Nat.le_add_right i z
                          )
                      ) (by linarith)
                  rw [← hnt]
                  exact List.getElem_drop' as.data
                have h7 : (slice as.data i z)[n]'h5 = as.data[n] := Eq.symm (is_prefix_eq as.data (slice as.data i z) hp h5)
                rw [← h6, ← h7]
            · have h₆ : (slice as.data i z).length + tail.length = as.data.length := by
                  nth_rewrite 2 [← hp']
                  exact Eq.symm (List.length_append (slice as.data i z) tail)
              rw [hz] at h₆
              have h₅ : n - (z + 1) < tail.length - 1 := by
                    calc n - (z + 1) < as.size - (z + 1) := by (exact Nat.sub_lt_sub_right (by linarith[hs]) h₂)
                  _ = as.data.length - (z + 1) := by simp
                  _ = z + tail.length - (z + 1) := by rw[← h₆]
                  _ = tail.length - 1 := Nat.add_sub_add_left z tail.length 1
              have h1 : (List.take (z + 1) (List.drop i as.data) ++ tail.tail)[n]'(by simp; exact h₁) =
                        tail.tail[n - (List.take (z + 1) (List.drop i as.data)).length]'(by simp; rw[hm]; exact h₅) := by
                apply List.getElem_append_right
                simp
                intro h
                push_neg at hs
                linarith
              rw [h1]
              simp

              have ht : tail.tail[n - min (z + 1) (as.data.length - i)]'(by rw [hm, List.length_tail tail]; exact h₅) =
                        tail.tail[n - (z + 1)]'(by rw [List.length_tail tail]; exact h₅) := getElem_congr (congrArg (HSub.hSub n) hm)
              rw [ht]
              clear ht

              have ht : as.data[n] = (slice as.data i z ++ tail)[n]'(by
                  simp
                  rw [hz, h₆]
                  exact h₂) :=
                List.getElem_of_eq hp'.symm h₂
              rw [ht]
              clear ht

              have hmw : n - (z + 1) < tail.tail.length := by
                  rw [List.length_tail tail]
                  exact h₅

              have ht : tail.tail[n - (z + 1)] = tail[n - z] := by
                have hi : tail.tail[n - (z + 1)] = tail.tail[n - z - 1] := by rfl
                rw [hi]
                have hj : tail[n - z] = tail[n - z - 1 + 1] := by
                  apply get_add_sub
                  exact tsub_pos_iff_not_le.mpr hs
                rw [hj]
                clear hj
                have h₂ : 0 < tail.length := by linarith
                have hin : n - (z + 1) = n - z - 1 := by rfl
                apply List.get_tail _ (n - z - 1) (by rw[List.length_tail tail, ←hin]; exact h₅) (by
                  rw [← hin]
                  calc n - (z + 1) + 1 < tail.length - 1 + 1 := by linarith
                       _ = tail.length := Nat.sub_add_cancel h₂
                  )
              rw [ht]
              clear ht

              rw [List.getElem_append_right (slice as.data i z) tail (by push_neg; rw [hz]; linarith)]
              exact getElem_congr (congrArg (HSub.hSub n) (hz.symm))
        ) b
      else
        {z := z, h := by
          constructor
          · exact hb
          · constructor
            ·
              unfold slice
              simp
              constructor
              · exact hp
              · exact List.take_prefix z (List.drop i as.data)
            · intro x hp'
              have ht : (slice as.data i z).length = z := by
                unfold slice
                simp
                exact Nat.le_sub_of_add_le' hb
              rw [ht]
              contrapose! he
              have hle : as[z] = x[z] := is_prefix_eq _ _ hp'.1 he
              rw [hle]
              let hp'2 := hp'.2
              let ls := List.drop i as.data
              have h3 : ls[z]'(List.lt_length_drop as.data b) = x[z] := is_prefix_eq ls x hp'2 he
              have h4 : ls[z]'(List.lt_length_drop as.data b) = as[i + z] := List.getElem_drop' as.data
              rw [← h4, h3]
        }
    else
      {z := z, h := by
        constructor
        · exact hb
        · constructor
          · simp
            constructor
            · exact hp
            · unfold slice
              exact List.take_prefix z (List.drop i as.data)
          · intro x hp'
            refine List.IsPrefix.length_le ?right.h
            unfold slice
            let hs := hp'.2
            push_neg at b
            refine List.prefix_take_iff.mpr ?right.h.a
            constructor
            · exact hp'.2
            · have h1 : x.length ≤ (as.data.drop i).length := List.IsPrefix.length_le hs
              have h2 : (as.data.drop i).length ≤ z := by
                simp
                linarith
              linarith
      }

def loop_build_table [BEq α] [DecidableEq α] (size i l r: ℕ) (zarray : PartialZArray as) (he : i = zarray.table.data.length) (hi : 0 < i) (hl : 0 < l) (hs : size + i = as.data.length) (hr : r ≤ as.data.length) (hg : l ≤ r) (hpre : slice as.data l (r - l) <+: as.data) (hlil : l ≤ i): ZArray (α := α) as :=
    match size with
    | 0 => ⟨zarray, by linarith[hs]⟩
    | n + 1 => (

      have hib : i - l < zarray.table.size := by
        calc i - l < i := by exact Nat.sub_lt hi hl
                 _ = zarray.table.size := he
      let t := min (r - i) (zarray.table[i - l]'(hib))

      let z := if i < r then t else 0

      let ⟨z, hz⟩ := loop_extend as i z (by
        by_cases hiz : i < r
        · have hzt : z = t := if_pos hiz
          rw [hzt]

          have ht : t ≤ r - i := Nat.min_le_left (r - i) zarray.table[i - l]
          have hlir : i ≤ r := Nat.le_of_succ_le hiz

          suffices slice as.data i t = as.data.take t by (
            rw [this]
            apply List.prefix_iff_eq_take.mpr
            simp
          )

          have h₃ : slice as.data l (r - l) = as.data.take (r - l) := by
            let hpre₁ := List.prefix_iff_eq_take.mp hpre
            rw [hpre₁]
            unfold slice
            simp
            have hl : r - l ≤ as.size - l := Nat.sub_le_sub_right hr l
            have hr : r - l ≤ as.size := by calc
              r - l ≤ as.size - l := by exact hl
                  _ ≤ as.size := by exact Nat.sub_le as.size l
            simp [hl, hr]

          have h₄ : slice as.data (i - l) t = as.data.take t := by
            have hb : i - l < zarray.table.data.length := by
              linarith
            have hl0 : t < as.size - (i - l) := by calc
              t ≤ r - i := ht
              _ ≤ as.size - i := Nat.sub_le_sub_right hr i
              _ < as.size - i + l := Nat.lt_add_of_pos_right hl
              _ = as.size + l - i := by (
                refine Eq.symm (Nat.sub_add_comm ?htt)
                exact Nat.le_trans hlir hr
              )
              _ = as.size - (i - l) := Nat.Simproc.add_sub_le as.size hlil

            let hpre := (zarray.is_z_function hb).right.left.left
            simp at hpre
            have hpres : slice as.data (i - l) t  <+: as.data := by
              suffices slice as.data (i - l) t <+: slice as.data (i - l) zarray.table[i - l] from List.IsPrefix.trans this hpre
              unfold slice
              refine (List.prefix_take_le_iff ?hm).mpr ?_
              · simp
                exact hl0
              · exact Nat.min_le_right (r - i) zarray.table[i - l]
            let hpre₁ := List.prefix_iff_eq_take.mp hpres
            rw [hpre₁]
            unfold slice
            simp

            have hl : t ≤ as.size - (i - l) := Nat.le_of_succ_le hl0
            have hr : t ≤ as.size := by calc
              t ≤ as.size - (i - l) := hl
              _ ≤ as.size := Nat.sub_le as.size (i - l)
            simp [hl, hr]

          have hl : i - l + t ≤ r - l := by
              calc i - l + t ≤ i - l + (r - i) := by exact Nat.add_le_add_left ht (i - l)
                           _ = i + (r - i) - l := Eq.symm (Nat.sub_add_comm hlil)
                           _ = r - l := by aesop

          have h₅ : slice as.data i t = slice (slice as.data l (r - l)) (i - l) t := by
            unfold slice
            nth_rewrite 2 [List.take_drop]
            rw [List.take_take, min_eq_left hl, List.drop_take]
            simp
            suffices i - l + l = i by (rw [this])
            exact Nat.sub_add_cancel hlil

          have h₆ : slice (List.take (r - l) as.data) (i - l) t = slice as.data (i - l) t := by
            unfold slice
            rw [List.take_drop, List.take_take, min_eq_left hl, List.drop_take]
            suffices i - l + t - (i - l) = t by (rw [this])
            simp
          rw [h₅, h₃, h₆, h₄]
        · have hz0 : z = 0 := if_neg hiz
          rw [hz0]
          unfold slice
          simp) (by
        by_cases hiz : i < r
        · have hzt : z = t := if_pos hiz
          have hlt : t ≤ r - i := Nat.min_le_left (r - i) zarray.table[i - l]
          have htr : i ≤ r := Nat.le_of_succ_le hiz
          calc i + z = i + t := by exact congrArg (HAdd.hAdd i) hzt
                   _ ≤ i + (r - i) := by linarith[hlt]
                   _ = r := Nat.add_sub_of_le htr
                   _ ≤ as.data.length := hr
        · have hz0 : z = 0 := if_neg hiz
          simp [hz0]
          simp at hs
          linarith
        )
      let new_table := zarray.table.push z
      have hnew_table_size : new_table.data.length = zarray.table.data.length + 1 := Array.size_push zarray.table z

      let new_zarray := ⟨new_table, by
        intro j hb'
        by_cases h : j < zarray.table.data.length
        · have hje : new_table.get ⟨j, hb'⟩ = zarray.table.get ⟨j, h⟩ := by
            apply Array.get_push_lt
          rw [hje]
          exact zarray.is_z_function h
        · simp
          have hiv : j = i := by
            push_neg at h
            rw [he]
            rw [hnew_table_size] at hb'
            linarith
          have hlast : new_table[j] = z := by
            rw [Array.get_push]
            simp
            intro h'
            contradiction
          rw [hlast]
          rw [hiv]
          exact hz
        ⟩

      if hnb : i + z > r then
        loop_build_table n (i + 1) i (i + z) (new_zarray) (by
          rw [he]; simp;
          exact Eq.symm (Array.size_push zarray.table z)
        ) (by linarith) hi (by linarith) hz.left (by linarith) (by
          suffices i + z - i = z by (rw[this]; exact hz.right.left.left)
          simp
        ) (by linarith)
      else
        loop_build_table n (i + 1) l r (new_zarray) (by
          rw [he]; simp;
          exact Eq.symm (Array.size_push zarray.table z)
        ) (by linarith) hl (by linarith) hr hg hpre (by linarith)
    )

def z_function [BEq α] [DecidableEq α] (as : Array α) : ZArray as :=
  if he : 0 = as.size
    then ZArray.empty as he
  else
    loop_build_table (as.size - 1) 1 1 1 (PartialZArray.init as) rfl (by trivial) (by trivial) (Nat.succ_pred_eq_of_ne_zero fun a ↦ he a.symm) (Nat.one_le_iff_ne_zero.mpr fun a ↦ he a.symm) (by trivial) (by unfold slice; simp) (by trivial)

#eval! (z_function #[1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 3]).z_array.table

end ZFunction
