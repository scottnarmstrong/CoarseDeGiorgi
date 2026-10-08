import CoarseDeGiorgi.LowerFractional.MeanNorm
import CoarseDeGiorgi.Foundations.Reconstruction.Geometry

/-! The cube-scaled mean inequality (e.fractional.mean.norm). -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory
open scoped ENNReal
open Foundations.Reconstruction

/-- Euclidean diameter bound with the exact auxiliary side length. -/
theorem auxCube_euclidDist_le {d : ℕ} (m : ℤ) (z : Fin d → ℤ)
    {x y : Vec d} (hx : x ∈ auxCube m z) (hy : y ∈ auxCube m z) :
    euclidDist x y ≤ Real.sqrt (d : ℝ) * auxSide m := by
  have hxy : dist x y ≤ auxSide m := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (auxSide_pos m).le).mpr
    intro i
    change |x i - y i| ≤ auxSide m
    have hb' : |x i - y i| ≤
        |x i - (z i : ℝ) * (3 : ℝ) ^ (-m)| +
          |y i - (z i : ℝ) * (3 : ℝ) ^ (-m)| := by
      simpa only [abs_sub_comm ((z i : ℝ) * (3 : ℝ) ^ (-m))] using
        abs_sub_le (x i) ((z i : ℝ) * (3 : ℝ) ^ (-m)) (y i)
    exact hb'.trans (by have hxi := hx i; have hyi := hy i; change _ < auxSide m / 2 at hxi hyi; linarith)
  exact (Foundations.Euclid.eDist2_le_sqrt_mul_dist x y).trans
    (mul_le_mul_of_nonneg_left hxy (Real.sqrt_nonneg _))

/-- Cancellation of the volume and diameter powers. -/
theorem mean_cube_coefficient {d : ℕ} [NeZero d] {r : ℝ} (hr : 0 < r)
    (α : ℝ) (m : ℤ) (z : Fin d → ℤ) :
    ((volume (auxCube m z)).toReal⁻¹ *
      (Real.sqrt (d : ℝ) * auxSide m) ^ ((d : ℝ) + α * r)) ^ (1 / r) =
      (Real.sqrt (d : ℝ)) ^ ((d : ℝ) / r + α) * (3 : ℝ) ^ α *
        (3 : ℝ) ^ (-(m : ℝ) * α) := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hS := auxSide_pos m
  rw [← auxCube_eq_statement, volume_auxCube, ENNReal.toReal_ofReal (pow_nonneg hS.le _),
    Real.mul_rpow (Real.sqrt_nonneg _) hS.le,
    Real.mul_rpow (inv_nonneg.mpr (pow_nonneg hS.le _))
      (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg hS.le _)),
    Real.mul_rpow (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg hS.le _),
    ← Real.rpow_natCast, ← Real.rpow_neg hS.le, ← Real.rpow_mul hS.le,
    ← Real.rpow_mul (Real.sqrt_nonneg _), ← Real.rpow_mul hS.le]
  have he : ((d : ℝ) + α * r) * (1 / r) = (d : ℝ) / r + α := by
    field_simp
  rw [he]
  rw [mul_left_comm, ← Real.rpow_add hS]
  have he' : -(d : ℝ) * (1 / r) + ((d : ℝ) / r + α) = α := by ring
  rw [he']
  unfold auxSide
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  push_cast
  rw [show (1 - (m : ℝ)) * α = α + -(m : ℝ) * α by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring

/-- Exact source mean estimate: the constant depends only on d, α and r. -/
theorem fractional_mean_norm_auxCube {d : ℕ} [NeZero d] {α r : ℝ}
    (hr : 1 ≤ r) (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ),
      AEStronglyMeasurable w (volume.restrict (auxCube m z)) →
      eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ (-(m : ℝ) * α)) *
          fracSeminorm (auxCube m z) α r w +
        ‖volumeAverage (auxCube m z) w‖ₑ * (volume (auxCube m z)) ^ (1 / r) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  let C := (Real.sqrt (d : ℝ)) ^ ((d : ℝ) / r + α) * (3 : ℝ) ^ α
  refine ⟨C, mul_pos (Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hd) _)
    (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro m z w hw
  have hb := fractional_mean_norm hr hα
    (mul_pos (Real.sqrt_pos.mpr hd) (auxSide_pos m))
    (measurableSet_auxCube m z) (volume_auxCube_ne_zero m z)
    (volume_auxCube_ne_top m z) (fun x hx y hy => auxCube_euclidDist_le m z hx hy) hw
  rw [auxCube_eq_statement] at hb
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofReal_rpow_of_nonneg
      (mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
        (Real.rpow_nonneg (mul_nonneg (Real.sqrt_nonneg _) (auxSide_pos m).le) _))
      (div_nonneg zero_le_one hr0.le), mean_cube_coefficient hr0] at hb
  exact hb


end CoarseDeGiorgi.LowerFractional
