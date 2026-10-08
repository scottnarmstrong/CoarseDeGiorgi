module

public import CoarseDeGiorgi.LowerFractional.TilingLocal

/-! The unit-cube containment forces nonnegative absolute scales. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization

lemma lower_aux_scale_nonneg {d : ℕ} [NeZero d] (m : ℤ) (z : Fin d → ℤ)
    (hQ : auxCube m z ⊆ Aliases.originCube 1) : 0 ≤ m := by
  let h : ℝ := (3 : ℝ) ^ (1 - m)
  have hh : 0 < h := zpow_pos (by norm_num) _
  let x : Vec d := fun i => (z i : ℝ) * (3 : ℝ) ^ (-m) + h / 3
  let y : Vec d := fun i => (z i : ℝ) * (3 : ℝ) ^ (-m) - h / 3
  have hx : x ∈ auxCube m z := by
    intro i
    change |(z i : ℝ) * (3 : ℝ) ^ (-m) + h / 3 - (z i : ℝ) * (3 : ℝ) ^ (-m)| < h / 2
    rw [add_sub_cancel_left, abs_of_pos (div_pos hh (by norm_num))]
    linarith only [hh]
  have hy : y ∈ auxCube m z := by
    intro i
    change |(z i : ℝ) * (3 : ℝ) ^ (-m) - h / 3 - (z i : ℝ) * (3 : ℝ) ^ (-m)| < h / 2
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (div_pos hh (by norm_num))]
    linarith only [hh]
  let i : Fin d := ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
  have hxi := hQ hx i
  have hyi := hQ hy i
  have hsmall : h < 3 / 2 := by
    change -(1 / 2 : ℝ) < (z i : ℝ) * (3 : ℝ) ^ (-m) + h / 3 ∧
      (z i : ℝ) * (3 : ℝ) ^ (-m) + h / 3 < 1 / 2 at hxi
    change -(1 / 2 : ℝ) < (z i : ℝ) * (3 : ℝ) ^ (-m) - h / 3 ∧
      (z i : ℝ) * (3 : ℝ) ^ (-m) - h / 3 < 1 / 2 at hyi
    linarith only [hxi.2, hyi.1]
  by_contra hm
  have hlarge : 3 ≤ h := by
    have he : (1 : ℤ) ≤ 1 - m := by omega
    simpa only [zpow_one] using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) he
  linarith only [hsmall, hlarge]


end CoarseDeGiorgi.LowerFractional
