module

public import CoarseDeGiorgi.Endpoint.Capacitary.Bounds

/-! Scalar cancellation for the source-mass estimate. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open scoped ENNReal

/-- Cancel the positive capacitary lower bound and combine the exponential factors.
The final constant depends only on the three constants selected before coefficients. -/
theorem capacitary_scalar_mass {κ A H R Z : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    {m Λ I : ℝ≥0∞} (hI : I ≠ ⊤)
    (h : ENNReal.ofReal (κ * Real.exp (-(H * Z))) * m ≤
      ENNReal.ofReal (Real.exp ((H + R) * Z) * I.toReal) * (ENNReal.ofReal A * Λ)) :
    m ≤ ENNReal.ofReal (A * κ⁻¹ + R + 2 * H) * Λ *
      ENNReal.ofReal (Real.exp ((A * κ⁻¹ + R + 2 * H) * Z)) * I := by
  let D : ℝ := A * κ⁻¹
  let C : ℝ := D + R + 2 * H
  have hD : 0 ≤ D := mul_nonneg hA (inv_nonneg.mpr hκ.le)
  have hDC : D ≤ C := by dsimp only [C]; linarith only [hR, hH]
  have hRC : R + 2 * H ≤ C := by dsimp only [C]; linarith only [hD]
  have hcancel : ENNReal.ofReal (κ⁻¹ * Real.exp (H * Z)) *
      ENNReal.ofReal (κ * Real.exp (-(H * Z))) = 1 := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hκ.le) (Real.exp_pos _).le)]
    have he : (κ⁻¹ * Real.exp (H * Z)) * (κ * Real.exp (-(H * Z))) = 1 := by
      calc
        _ = (κ⁻¹ * κ) * (Real.exp (H * Z) * Real.exp (-(H * Z))) := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hκ.ne', ← Real.exp_add]; simp
    rw [he]
    norm_num
  have hc := mul_le_mul_right h (ENNReal.ofReal (κ⁻¹ * Real.exp (H * Z)))
  rw [← mul_assoc, hcancel, one_mul] at hc
  have hfactor : ENNReal.ofReal (κ⁻¹ * Real.exp (H * Z)) *
      (ENNReal.ofReal (Real.exp ((H + R) * Z) * I.toReal) * (ENNReal.ofReal A * Λ)) =
      ENNReal.ofReal D * Λ * ENNReal.ofReal (Real.exp ((R + 2 * H) * Z)) * I := by
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le),
      ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hI]
    have hexp : ENNReal.ofReal (Real.exp (H * Z)) *
        ENNReal.ofReal (Real.exp ((H + R) * Z)) =
        ENNReal.ofReal (Real.exp ((R + 2 * H) * Z)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    rw [show ENNReal.ofReal D = ENNReal.ofReal A * ENNReal.ofReal κ⁻¹ from
      ENNReal.ofReal_mul hA, ← hexp]
    ac_rfl
  rw [hfactor] at hc
  have he : ENNReal.ofReal (Real.exp ((R + 2 * H) * Z)) ≤
      ENNReal.ofReal (Real.exp (C * Z)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hRC hZ))
  exact hc.trans (mul_le_mul_left
    (mul_le_mul (mul_le_mul_left (ENNReal.ofReal_le_ofReal hDC) Λ) he zero_le zero_le) I)

end CoarseDeGiorgi.Endpoint
