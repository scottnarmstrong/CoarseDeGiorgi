import CoarseDeGiorgi.Assembly.HybridParameters
import CoarseDeGiorgi.Assembly.HybridQuantity

namespace CoarseDeGiorgi.Assembly
open scoped ENNReal

/-- Multiply the selected controls and normalize by the lower moment. Both
radius powers remain exact; an infinite lower moment is allowed. -/
theorem hybrid_normalized_surface_bound {δ h Δ a b θ m z : ℝ}
    (hδ : 0 < δ) (hz : 0 ≤ z)
    {Ks Kd Kf Kl Kseed U L E Y S D F Z X : ℝ≥0∞}
    (hS : S ≤ Ks * ENNReal.ofReal δ ^ (-a) * U ^ (1 / 2 : ℝ))
    (hD : D ^ (1 / 2 : ℝ) ≤ Kd * ENNReal.ofReal δ ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ))
    (hF : F ≤ Kf * ENNReal.ofReal δ ^ (-b) * Y)
    (hZ : Z ≤ Kl * ENNReal.ofReal δ ^ (-b * z / 2) * Y ^ (z / 2) *
      ENNReal.ofReal Δ ^ (1 - z / 2))
    (hY : L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) ≤ Y)
    (hX : X ≤ Kseed * S * D ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal h ^ θ * F + ENNReal.ofReal h ^ (-m) * Z)) :
    L ^ (-1 : ℝ) * X ≤
      (Kseed * Ks * Kd * Kf) * ENNReal.ofReal δ ^ (-(a + 1 / 2 + b)) *
        (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ θ * Y ^ (2 : ℝ) +
      (Kseed * Ks * Kd * Kl) * ENNReal.ofReal δ ^ (-(a + 1 / 2 + b * z / 2)) *
        (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ (-m) *
        Y ^ (1 + z / 2) * ENNReal.ofReal Δ ^ (1 - z / 2) := by
  let P := ENNReal.ofReal δ
  have hP : P ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hL : L ^ (-1 : ℝ) = L ^ (-1 / 2 : ℝ) * L ^ (-1 / 2 : ℝ) := by
    by_cases h0 : L = 0
    · norm_num [h0]
    by_cases ht : L = ⊤
    · norm_num [ht]
    rw [← ENNReal.rpow_add _ _ h0 ht]
    norm_num
  have hUL : (U / L) ^ (1 / 2 : ℝ) = U ^ (1 / 2 : ℝ) * L ^ (-1 / 2 : ℝ) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), div_eq_mul_inv]
    congr 1
    simpa only [neg_div] using (ENNReal.rpow_neg L (1 / 2 : ℝ)).symm
  have hp (c : ℝ) : P ^ (-a) * P ^ (-1 / 2 : ℝ) * P ^ (-c) = P ^ (-(a + 1 / 2 + c)) := by
    rw [← ENNReal.rpow_add _ _ hP hPt, ← ENNReal.rpow_add _ _ hP hPt]
    congr 1
    ring
  have hy : Y * Y = Y ^ (2 : ℝ) := by rw [ENNReal.rpow_two, pow_two]
  have hyz : Y * Y ^ (z / 2) = Y ^ (1 + z / 2) := by
    rw [ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by positivity), ENNReal.rpow_one]
  calc
    _ ≤ L ^ (-1 : ℝ) * (Kseed * (Ks * P ^ (-a) * U ^ (1 / 2 : ℝ)) *
        (Kd * P ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) *
        (ENNReal.ofReal h ^ θ * (Kf * P ^ (-b) * Y) +
          ENNReal.ofReal h ^ (-m) * (Kl * P ^ (-b * z / 2) * Y ^ (z / 2) *
            ENNReal.ofReal Δ ^ (1 - z / 2)))) := by
      apply mul_le_mul_right (hX.trans _) _
      exact mul_le_mul' (mul_le_mul' (mul_le_mul_right hS Kseed) hD)
        (add_le_add (mul_le_mul_right hF _) (mul_le_mul_right hZ _))
    _ = (Kseed * Ks * Kd * Kf) * P ^ (-(a + 1 / 2 + b)) *
        (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ θ *
        (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) * Y +
      (Kseed * Ks * Kd * Kl) * P ^ (-(a + 1 / 2 + b * z / 2)) *
        (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ (-m) *
        (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) * Y ^ (z / 2) * ENNReal.ofReal Δ ^ (1 - z / 2) := by
      rw [hL, hUL, ← hp b, ← hp (b * z / 2)]
      dsimp only [P]
      ring_nf
    _ ≤ _ := by
      have h₁ : (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) * Y ≤ Y * Y := mul_le_mul' hY le_rfl
      have h₂ : (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) * Y ^ (z / 2) ≤ Y * Y ^ (z / 2) := mul_le_mul' hY le_rfl
      rw [hy] at h₁
      rw [hyz] at h₂
      convert add_le_add
        (mul_le_mul_right h₁ ((Kseed * Ks * Kd * Kf) * P ^ (-(a + 1 / 2 + b)) *
          (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ θ))
        (mul_le_mul' (mul_le_mul_right h₂ ((Kseed * Ks * Kd * Kl) * P ^ (-(a + 1 / 2 + b * z / 2)) *
          (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ (-m))) le_rfl) using 1
      all_goals (dsimp only [P]; ring)

end CoarseDeGiorgi.Assembly
