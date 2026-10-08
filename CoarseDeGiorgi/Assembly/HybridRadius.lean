import CoarseDeGiorgi.Localization.SourceCover
import CoarseDeGiorgi.Localization.LowerFractional

namespace CoarseDeGiorgi.Assembly

open scoped ENNReal

/-- Convert the two localization losses to their common radius power.
The constant is independent of the radius, finite cover, and function data. -/
theorem hybrid_localization_radius_bound {d : ℕ} {C : ℝ≥0∞} {α r γ : ℝ}
    (hC : C ≠ ⊤) (hC0 : 0 < C) (hr : 0 < r) (hr2 : r < 2)
    (hαγ : α ≤ γ) (hcardγ : (d : ℝ) * (1 - r / 2) ≤ γ * r) :
    ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
      ∀ (δ : ℝ) (n : ℕ) (L N F Y : ℝ≥0∞),
      0 < δ → δ ≤ 1 → (n : ℝ) ≤ (960 : ℝ) ^ d * δ ^ (-(d : ℝ)) →
      L ≤ Y → N ≤ Y →
      F ^ r ≤ C * (n : ℝ≥0∞) ^ (1 - r / 2) * ((4 ^ d : ℕ) : ℝ≥0∞) ^ (r / 2) * L ^ r +
        C * ENNReal.ofReal (δ ^ (-α * r)) * ((4 ^ d : ℕ) : ℝ≥0∞) * N ^ r →
      F ≤ K * ENNReal.ofReal (δ ^ (-γ)) * Y := by
  let A : ℝ≥0∞ := ENNReal.ofReal ((960 : ℝ) ^ d) ^ (1 - r / 2)
  let O : ℝ≥0∞ := ((4 ^ d : ℕ) : ℝ≥0∞)
  let B := C * (A * O ^ (r / 2) + O)
  have ha : 0 < 1 - r / 2 := by linarith only [hr2]
  have hB0 : 0 < B := by dsimp [B, A, O]; positivity
  have hB : B ≠ ⊤ := by dsimp [B, A, O]; finiteness
  refine ⟨B ^ (1 / r), by positivity,
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hB, ?_⟩
  intro δ n L N F Y hδ hδ1 hn hL hN hbound
  let P : ℝ≥0∞ := ENNReal.ofReal (δ ^ (-γ * r))
  have hc : (n : ℝ≥0∞) ^ (1 - r / 2) ≤ A * P := by
    have hn' : (n : ℝ≥0∞) ≤ ENNReal.ofReal ((960 : ℝ) ^ d * δ ^ (-(d : ℝ))) := by
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hn
    have h := ENNReal.rpow_le_rpow hn' ha.le
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ ha.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hδ.le _) ha.le,
      ← Real.rpow_mul hδ.le] at h
    have hp : δ ^ (-(d : ℝ) * (1 - r / 2)) ≤ δ ^ (-γ * r) :=
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith only [hcardγ])
    exact h.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hp) _)
  have hm : ENNReal.ofReal (δ ^ (-α * r)) ≤ P := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      (by simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hαγ hr.le))
  have hpow : F ^ r ≤ B * P * Y ^ r := by
    calc
      _ ≤ C * (n : ℝ≥0∞) ^ (1 - r / 2) * O ^ (r / 2) * L ^ r +
          C * ENNReal.ofReal (δ ^ (-α * r)) * O * N ^ r := hbound
      _ ≤ C * (A * P) * O ^ (r / 2) * Y ^ r + C * P * O * Y ^ r := by
        gcongr
      _ = _ := by dsimp [B]; ring
  have h := ENNReal.rpow_le_rpow hpow (show 0 ≤ 1 / r by positivity)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one] at h
  have hP : P ^ (1 / r) = ENNReal.ofReal (δ ^ (-γ)) := by
    dsimp [P]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hδ.le _) (by positivity),
      ← Real.rpow_mul hδ.le, show (-γ * r) * (1 / r) = -γ by field_simp]
  simpa only [hP] using h

end CoarseDeGiorgi.Assembly
