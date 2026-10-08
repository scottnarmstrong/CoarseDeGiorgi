import CoarseDeGiorgi.Harnack.Iterations.SmallMomentStep

open scoped ENNReal
namespace CoarseDeGiorgi.Harnack.Iterations

/-- The geometric contrast bound gives the logarithmic cost used by both endpoint chains.
-/
theorem geometric_reverse_cost_le_exp {C Θ : ℝ≥0∞} {δ γ r β m χ : ℝ} (j : ℕ) (hχ : 1 < χ)
    (hC : 1 ≤ C) (hCtop : C < ⊤) (hΘtop : Θ < ⊤)
    (hδ : 0 < δ) (_hr : 0 < r) (hβ : 0 ≤ β)
    (hfactor : powerFactor m ^ 2 * Θ.toReal ≤ χ ^ (2 * j)) :
    C * (ENNReal.ofReal ((δ / 2) ^ (-γ))) ^ r *
      (1 + ENNReal.ofReal (powerFactor m ^ 2) * Θ) ^ β ≤
    ENNReal.ofReal (Real.exp (Real.log C.toReal +
      (γ * r + β) * Real.log 2 + γ * r * Real.log (1 / δ) +
        2 * β * (j : ℝ) * Real.log χ)) := by
  have hCReal : 1 ≤ C.toReal := by
    simpa using ENNReal.toReal_mono hCtop.ne hC
  have hCRealPos : 0 < C.toReal := zero_lt_one.trans_le hCReal
  have hχpos := zero_lt_one.trans hχ
  have hx : ENNReal.ofReal (powerFactor m ^ 2) * Θ ≤
      ENNReal.ofReal (χ ^ (2 * j)) := by
    calc
      _ = ENNReal.ofReal (powerFactor m ^ 2 * Θ.toReal) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_toReal hΘtop.ne]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hfactor
  have hpow : 1 ≤ χ ^ (2 * j) := one_le_pow₀ hχ.le
  have hx2 : 1 + ENNReal.ofReal (powerFactor m ^ 2) * Θ ≤
      ENNReal.ofReal (2 * χ ^ (2 * j)) := by
    calc
      _ ≤ ENNReal.ofReal (χ ^ (2 * j)) + ENNReal.ofReal (χ ^ (2 * j)) :=
        add_le_add (by simpa using ENNReal.ofReal_le_ofReal hpow) hx
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hhalf : 0 < δ / 2 := by positivity
  calc
    _ ≤ C * (ENNReal.ofReal ((δ / 2) ^ (-γ))) ^ r * (ENNReal.ofReal (2 * χ ^ (2 * j))) ^ β :=
      mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hx2 hβ) zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_toReal hCtop.ne,
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hhalf _)]
      rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < 2 * χ ^ (2 * j))]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C.toReal),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ C.toReal * ((δ / 2) ^ (-γ)) ^ r)]
      congr 1
      rw [Real.rpow_def_of_pos hhalf, ← Real.exp_mul,
        Real.rpow_def_of_pos (by positivity : (0 : ℝ) < 2 * χ ^ (2 * j)),
        ← Real.exp_log hCRealPos, ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [Real.log_div hδ.ne' (by norm_num : (2 : ℝ) ≠ 0), one_div, Real.log_inv]
      simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hχpos.ne'),
        Real.log_pow]
      push_cast
      ring

end CoarseDeGiorgi.Harnack.Iterations
