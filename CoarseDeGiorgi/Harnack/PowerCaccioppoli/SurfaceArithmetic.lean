import CoarseDeGiorgi.Assembly.CaccioppoliDefs
import CoarseDeGiorgi.Assembly.CaccioppoliParameters

/-! # Collect the selected signed-power surface bounds -/

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open scoped ENNReal

/-- The source's three selected controls imply the uniform one-surface bound.
The two trace terms containing the volume norm share one coefficient; this
costs a factor of two and does not change its dependence on the power. -/
theorem selected_surface_arithmetic
    {δ h a b c θ σ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hh1 : h ≤ 1)
    (hcb : c ≤ b) (hθσ : -σ ≤ θ)
    (cm Cext K U L E Y S D F Z X : ℝ≥0∞)
    (hS : S ≤ K * ENNReal.ofReal δ ^ (-a) * U ^ (1 / 2 : ℝ))
    (hD : D ≤ K * ENNReal.ofReal δ ^ (-1 : ℝ) * E)
    (hF : F ≤ K * ENNReal.ofReal δ ^ (-b) *
      (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + Y))
    (hZ : Z ≤ K * ENNReal.ofReal δ ^ (-c) * Y)
    (hX : X ≤ cm * Cext * S * D ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal h ^ θ * F + ENNReal.ofReal h ^ (-σ) * Z)) :
    X ≤ (2 * Cext * K * K ^ (1 / 2 : ℝ) * K) *
      ENNReal.ofReal δ ^ (-(a + 1 / 2 + b)) *
      (cm * (U / L) ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ θ * E +
        cm * U ^ (1 / 2 : ℝ) * ENNReal.ofReal h ^ (-σ) * Y * E ^ (1 / 2 : ℝ)) := by
  let P := ENNReal.ofReal δ
  let Q := ENNReal.ofReal h
  let A := Cext * K * K ^ (1 / 2 : ℝ) * K
  have hP0 : P ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP1 : P ≤ 1 := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hδ1
  have hQ1 : Q ≤ 1 := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hh1
  have hDbound : D ^ (1 / 2 : ℝ) ≤
      K ^ (1 / 2 : ℝ) * P ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by
    have hb := ENNReal.rpow_le_rpow hD (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at hb
    norm_num at hb
    simpa only [P, neg_div] using hb
  have hQle : Q ^ θ ≤ Q ^ (-σ) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hQ1 hθσ
  have hPle : P ^ (-(a + 1 / 2 + c)) ≤ P ^ (-(a + 1 / 2 + b)) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hP1 (by linarith only [hcb])
  have hpower (z : ℝ) : P ^ (-a) * P ^ (-1 / 2 : ℝ) * P ^ (-z) =
      P ^ (-(a + 1 / 2 + z)) := by
    rw [← ENNReal.rpow_add _ _ hP0 hPt, ← ENNReal.rpow_add _ _ hP0 hPt]
    congr 1
    ring
  have hUL : (U / L) ^ (1 / 2 : ℝ) = U ^ (1 / 2 : ℝ) * L ^ (-1 / 2 : ℝ) := by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), div_eq_mul_inv]
    congr 1
    simpa only [neg_div] using (ENNReal.rpow_neg L (1 / 2 : ℝ)).symm
  have hEE : E ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) = E := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  let T := cm * (U / L) ^ (1 / 2 : ℝ) * Q ^ θ * E
  let W := cm * U ^ (1 / 2 : ℝ) * Q ^ (-σ) * Y * E ^ (1 / 2 : ℝ)
  calc
    X ≤ cm * Cext * (K * P ^ (-a) * U ^ (1 / 2 : ℝ)) *
        (K ^ (1 / 2 : ℝ) * P ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) *
        (Q ^ θ * (K * P ^ (-b) * (L ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + Y)) +
          Q ^ (-σ) * (K * P ^ (-c) * Y)) := by
      apply hX.trans
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hS) hDbound)
        (add_le_add (mul_le_mul' le_rfl hF) (mul_le_mul' le_rfl hZ))
    _ = A * P ^ (-(a + 1 / 2 + b)) * T +
        A * P ^ (-(a + 1 / 2 + b)) *
          (cm * U ^ (1 / 2 : ℝ) * Q ^ θ * Y * E ^ (1 / 2 : ℝ)) +
        A * P ^ (-(a + 1 / 2 + c)) * W := by
      dsimp only [A, T, W]
      rw [hUL, ← hpower b, ← hpower c]
      have hEEpow : (E ^ (1 / 2 : ℝ)) ^ 2 = E := by rw [pow_two, hEE]
      ring_nf
      rw [hEEpow]
      ring
    _ ≤ A * P ^ (-(a + 1 / 2 + b)) * T +
        A * P ^ (-(a + 1 / 2 + b)) * W +
        A * P ^ (-(a + 1 / 2 + b)) * W := by
      dsimp only [W]
      gcongr
    _ ≤ (2 * A) * P ^ (-(a + 1 / 2 + b)) * (T + W) := by
      calc
        _ ≤ A * P ^ (-(a + 1 / 2 + b)) * T +
            A * P ^ (-(a + 1 / 2 + b)) * T +
            A * P ^ (-(a + 1 / 2 + b)) * W +
            A * P ^ (-(a + 1 / 2 + b)) * W := by
          exact add_le_add (add_le_add (le_add_right le_rfl) le_rfl) le_rfl
        _ = _ := by ring
    _ = _ := by dsimp only [A, T, W, P, Q]; ring

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
