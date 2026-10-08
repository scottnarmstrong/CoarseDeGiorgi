import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Algebra of one layer of the exterior integral -/

namespace CoarseDeGiorgi.ExteriorIntegral

open scoped ENNReal

noncomputable section

theorem sqrt_sq_eq (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem sqrt_add_sq_le (X Y : ℝ≥0∞) : (X ^ 2 + Y ^ 2) ^ (1 / 2 : ℝ) ≤ X + Y := by
  have h : X ^ 2 + Y ^ 2 ≤ (X + Y) ^ 2 := by
    have : (X + Y) ^ 2 = X ^ 2 + Y ^ 2 + 2 * (X * Y) := by ring
    rw [this]
    exact le_self_add
  calc (X ^ 2 + Y ^ 2) ^ (1 / 2 : ℝ) ≤ ((X + Y) ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = X + Y := sqrt_sq_eq _

theorem sqrt_mul_self (ℓ : ℝ≥0∞) : (ℓ * ℓ) ^ (1 / 2 : ℝ) = ℓ := by
  rw [← pow_two]
  exact sqrt_sq_eq ℓ

/-- The square root of the product of the two layer bounds. -/
theorem layer_product_bound (A C ℓ u F w L D : ℝ≥0∞) :
    (A * (C * ℓ * (u * F) ^ 2 + C * ℓ * (w * L) ^ 2)) ^ (1 / 2 : ℝ) *
        (54 * ℓ * D) ^ (1 / 2 : ℝ) ≤
      (54 * C) ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) *
        (ℓ * u * F + ℓ * w * L) := by
  have hnn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hnn]
  have hin : A * (C * ℓ * (u * F) ^ 2 + C * ℓ * (w * L) ^ 2) * (54 * ℓ * D) =
      (54 * C) * A * D * (ℓ * ℓ) * ((u * F) ^ 2 + (w * L) ^ 2) := by ring
  rw [hin, ENNReal.mul_rpow_of_nonneg _ _ hnn, ENNReal.mul_rpow_of_nonneg _ _ hnn,
    ENNReal.mul_rpow_of_nonneg _ _ hnn, ENNReal.mul_rpow_of_nonneg _ _ hnn, sqrt_mul_self]
  calc _ ≤ (54 * C) ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ) * ℓ *
        (u * F + w * L) := by
        gcongr
        exact sqrt_add_sq_le _ _
    _ = _ := by ring

theorem rpow_ofReal_pos {h : ℝ} (hh : 0 < h) (p : ℝ) :
    (ENNReal.ofReal h) ^ p = ENNReal.ofReal (h ^ p) :=
  ENNReal.ofReal_rpow_of_pos hh

/-- First exponent comparison: `3^{-j} 3^{j} 3^{-jγ} ≤ 3^{-jσ} h^θ` for `γ = σ + θ`. -/
theorem exponent_one (j : ℕ) {σ θ γ h : ℝ} (hθ : 0 < θ) (hγ : γ = σ + θ) (hh : 0 < h)
    (hl : (3 : ℝ) ^ (-(j : ℤ)) ≤ h) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
        ENNReal.ofReal ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-((j : ℝ) * γ))) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-((j : ℝ) * σ))) * (ENNReal.ofReal h) ^ θ := by
  rw [rpow_ofReal_pos hh, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hl0 : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := by positivity
  have e1 : (3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (j : ℤ) = 1 := by
    rw [← zpow_add₀ h3.ne']; simp
  have e2 : (3 : ℝ) ^ (-((j : ℝ) * γ)) = (3 : ℝ) ^ (-((j : ℝ) * σ)) *
      ((3 : ℝ) ^ (-(j : ℤ))) ^ θ := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul h3.le, ← Real.rpow_add h3, hγ]
    congr 1
    push_cast
    ring
  calc (3 : ℝ) ^ (-(j : ℤ)) * ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (-((j : ℝ) * γ)))
      = ((3 : ℝ) ^ (-(j : ℤ)) * (3 : ℝ) ^ (j : ℤ)) * (3 : ℝ) ^ (-((j : ℝ) * γ)) := by ring
    _ = (3 : ℝ) ^ (-((j : ℝ) * σ)) * ((3 : ℝ) ^ (-(j : ℤ))) ^ θ := by rw [e1, one_mul, e2]
    _ ≤ _ := by
      gcongr

/-- Second exponent comparison. -/
theorem exponent_two (j : ℕ) {σ β h : ℝ} (he : 0 ≤ 1 - σ - β) (hh : 0 < h)
    (hl : (3 : ℝ) ^ (-(j : ℤ)) ≤ h) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(j : ℤ))) *
        ENNReal.ofReal (h⁻¹ * (3 : ℝ) ^ ((j : ℝ) * β)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-((j : ℝ) * σ))) * (ENNReal.ofReal h) ^ (-(σ + β)) := by
  rw [rpow_ofReal_pos hh, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h3 : (0 : ℝ) < 3 := by norm_num
  set l : ℝ := (3 : ℝ) ^ (-(j : ℤ)) with hldef
  have hl0 : 0 < l := by positivity
  have hlr : l = (3 : ℝ) ^ (-(j : ℝ)) := by
    rw [hldef, ← Real.rpow_intCast]; simp
  have e3 : (3 : ℝ) ^ ((j : ℝ) * β) = l ^ (-β) := by
    rw [hlr, ← Real.rpow_mul h3.le]; congr 1; ring
  have e4 : (3 : ℝ) ^ (-((j : ℝ) * σ)) = l ^ σ := by
    rw [hlr, ← Real.rpow_mul h3.le]; congr 1; ring
  have e5 : l * l ^ (-β) = l ^ σ * l ^ (1 - σ - β) := by
    have a1 : l * l ^ (-β) = l ^ (1 + -β) := by
      rw [Real.rpow_add hl0, Real.rpow_one]
    have a2 : l ^ σ * l ^ (1 - σ - β) = l ^ (σ + (1 - σ - β)) := by
      rw [Real.rpow_add hl0]
    rw [a1, a2]
    congr 1
    ring
  have e6 : h ^ (-(σ + β)) = h ^ (1 - σ - β) * h⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hh]
    congr 1
    ring
  have e7 : l ^ (1 - σ - β) ≤ h ^ (1 - σ - β) := Real.rpow_le_rpow hl0.le hl he
  rw [e3, e4, e6]
  calc l * (h⁻¹ * l ^ (-β)) = (l * l ^ (-β)) * h⁻¹ := by ring
    _ = l ^ σ * l ^ (1 - σ - β) * h⁻¹ := by rw [e5]
    _ ≤ l ^ σ * h ^ (1 - σ - β) * h⁻¹ := by gcongr
    _ = _ := by ring

end

end CoarseDeGiorgi.ExteriorIntegral
