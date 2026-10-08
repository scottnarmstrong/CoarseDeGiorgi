import CoarseDeGiorgi.Endpoint.Reconstruction.StepInverse

/-! # Exact triadic powers in the block estimates -/

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open scoped ENNReal

theorem triadic_side_rpow (k : ℕ) (a : ℝ) :
    (((3 : ℝ) ^ (-(k : ℤ))) : ℝ) ^ a = (3 : ℝ) ^ (-(k : ℝ) * a) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [Int.cast_neg, Int.cast_natCast]

theorem cell_volume_rpow {d : ℕ} (k : ℕ) (a : ℝ) :
    (ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℤ))) ^ d)) ^ a =
      ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ) * d * a)) := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity), triadic_side_rpow]
  congr 2
  ring

theorem side_mul_cell_volume_rpow {d : ℕ} (k : ℕ) (h a : ℝ) :
    ENNReal.ofReal ((((3 : ℝ) ^ (-(k : ℤ))) : ℝ) ^ h) *
      (ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℤ))) ^ d)) ^ a =
      ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℝ) * (h + d * a))) := by
  rw [cell_volume_rpow, triadic_side_rpow, ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 2
  ring

theorem morrey_cell_scale {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (r : ℝ) :
    ENNReal.ofReal ((((3 : ℝ) ^ (-(k : ℤ))) : ℝ) ^ (1 / 2 : ℝ)) *
      (ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℤ))) ^ d)) ^ (1 / (2 * d) - 1 / r) =
      ENNReal.ofReal ((3 : ℝ) ^ ((k : ℝ) * ((d : ℝ) / r - 1))) := by
  rw [side_mul_cell_volume_rpow]
  congr 2
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  field_simp
  ring

theorem parent_scale_eq_three_mul_child (k : ℕ) :
    (3 : ℝ) ^ (-(k : ℤ)) = 3 * (3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
  conv_rhs => lhs; rw [← zpow_one (3 : ℝ)]
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 1
  omega

theorem mean_parent_cell_scale {d : ℕ} (k : ℕ) (r : ℝ) :
    (ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ d)) ^ (-(1 / r)) *
      ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℤ))) =
      ENNReal.ofReal (3 : ℝ) *
        ENNReal.ofReal ((3 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * ((d : ℝ) / r - 1))) := by
  rw [parent_scale_eq_three_mul_child k, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hh := side_mul_cell_volume_rpow (d := d) (k + 1) 1 (-(1 / r))
  rw [Real.rpow_one] at hh
  calc
    _ = ENNReal.ofReal (3 : ℝ) *
        (ENNReal.ofReal ((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) *
          (ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ d)) ^ (-(1 / r))) := by ring
    _ = _ := by
      rw [hh]
      have he : -(((k + 1 : ℕ) : ℝ)) * (1 + (d : ℝ) * -(1 / r)) =
          (((k + 1 : ℕ) : ℝ)) * ((d : ℝ) / r - 1) := by ring
      rw [he]

end CoarseDeGiorgi.Endpoint.Reconstruction
