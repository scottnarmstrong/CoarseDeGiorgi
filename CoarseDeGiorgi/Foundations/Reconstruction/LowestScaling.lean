import CoarseDeGiorgi.Foundations.Reconstruction.LowestKernel

/-! # Exact scaling of the lowest periodic kernel -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory

noncomputable section

/-- Unit-side reference scale. -/
theorem auxSide_one : auxSide 1 = 1 := by norm_num [auxSide]

/-- Coordinate reduction commutes with positive rescaling of the period. -/
theorem wrapCoordinate_scale (m : ℤ) (t : ℝ) :
    wrapCoordinate m t = auxSide m * wrapCoordinate 1 ((auxSide m)⁻¹ * t) := by
  unfold wrapCoordinate
  rw [toIcoMod_eq_add_fract_mul, toIcoMod_eq_add_fract_mul, auxSide_one]
  have heq : ((auxSide m)⁻¹ * t - -(1 : ℝ)) / (2 * 1) =
      (t - -auxSide m) / (2 * auxSide m) := by
    field_simp [(auxSide_pos m).ne']
  rw [heq]
  ring

theorem lowestDensity_scale (m : ℤ) (t : ℝ) :
    lowestDensity m t = (auxSide m)⁻¹ * lowestDensity 1 ((auxSide m)⁻¹ * t) := by
  rw [lowestDensity_eq, lowestDensity_eq, auxSide_one, wrapCoordinate_scale]
  simp only [scaledEta, inv_one, one_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (auxSide_pos m).ne', one_mul]

theorem lowestMeanDensity_scale (m : ℤ) :
    lowestMeanDensity m = (auxSide m)⁻¹ * lowestMeanDensity 1 := by
  simp only [lowestMeanDensity, auxSide_one, mul_one, mul_inv_rev]

/-- The primitive is dimensionless under physical scaling. -/
theorem lowestPrimitive_scale (m : ℤ) (t : ℝ) :
    lowestPrimitive m t = lowestPrimitive 1 ((auxSide m)⁻¹ * t) := by
  unfold lowestPrimitive
  rw [auxSide_one]
  simp_rw [lowestDensity_scale m, lowestMeanDensity_scale m, ← mul_sub]
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_mul_left
    (fun s => lowestDensity 1 s - lowestMeanDensity 1)
    (inv_ne_zero (auxSide_pos m).ne') (a := -auxSide m) (b := t)
  simp only [inv_inv, smul_eq_mul] at h
  rw [h, mul_neg, inv_mul_cancel₀ (auxSide_pos m).ne',
    ← mul_assoc, inv_mul_cancel₀ (auxSide_pos m).ne', one_mul]

/-- Every lowest kernel is a rescaled unit-period kernel. -/
theorem lowestKernel_scale (m : ℤ) (d : ℕ) (v : Vec d) :
    lowestKernel m d v = (auxSide m * ((auxSide m) ^ d)⁻¹) •
      lowestKernel 1 d ((auxSide m)⁻¹ • v) := by
  induction d with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [lowestKernel, Fin.cases_zero, Pi.smul_apply, smul_eq_mul,
        pow_succ, mul_inv_rev]
      rw [lowestPrimitive_scale m, lowestMeanDensity_scale m, mul_pow]
      rw [show auxSide m * ((auxSide m)⁻¹ * ((auxSide m) ^ n)⁻¹) =
        ((auxSide m)⁻¹) ^ n by
          rw [← mul_assoc, mul_inv_cancel₀ (auxSide_pos m).ne', one_mul, inv_pow]]
      ring
    · simp only [lowestKernel, Fin.cases_succ, Pi.smul_apply, smul_eq_mul,
        pow_succ, mul_inv_rev]
      rw [lowestDensity_scale m, ih]
      simp only [Pi.smul_apply, smul_eq_mul]
      have heq : Fin.tail ((auxSide m)⁻¹ • v) = (auxSide m)⁻¹ • Fin.tail v := rfl
      rw [heq]
      ring

end

end CoarseDeGiorgi.Foundations.Reconstruction
