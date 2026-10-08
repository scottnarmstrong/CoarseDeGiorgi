import CoarseDeGiorgi.LowerFractional.Aliases
import CoarseDeGiorgi.Statements.FracNorm

/-! Elementary comparisons for the actual weighted and fractional norms. -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped ENNReal

lemma lower_weighted_energy_norm_le {d : ℕ} (a : CoeffField d) (Q : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) :
    (weightedEnergy a Q G) ^ (1 / 2 : ℝ) ≤ h1aWeightedNorm a Q w G := by
  exact ENNReal.rpow_le_rpow (le_add_self) (by norm_num)

lemma lower_weighted_mean_norm_le {d : ℕ} (a : CoeffField d) (Q : Set (Vec d))
    (w : Vec d → ℝ) (G : Vec d → Vec d) :
    ‖volumeAverage Q w‖ₑ ≤ h1aWeightedNorm a Q w G := by
  have he : ‖volumeAverage Q w‖ₑ ^ (2 : ℕ) = ENNReal.ofReal ((volumeAverage Q w) ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2, Real.norm_eq_abs, sq_abs]
  have hh := ENNReal.rpow_le_rpow (x := ENNReal.ofReal ((volumeAverage Q w) ^ 2))
    (y := ENNReal.ofReal ((volumeAverage Q w) ^ 2) + weightedEnergy a Q G)
    le_self_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [← he, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hh
  norm_num at hh
  rw [he] at hh
  exact hh

lemma lower_fracNorm_bound {d : ℕ} {Q : Set (Vec d)} {α r : ℝ}
    (hr : 0 < r) (w : Vec d → ℝ) (A B H : ℝ≥0∞)
    (hLp : eLpNorm w (ENNReal.ofReal r) (volume.restrict Q) ≤ A * H)
    (hsemi : fracSeminorm Q α r w ≤ B * H) :
    fracNorm Q α r w ≤ (A ^ r + B ^ r) ^ (1 / r) * H := by
  have hh := ENNReal.rpow_le_rpow
    (add_le_add (ENNReal.rpow_le_rpow hLp hr.le) (ENNReal.rpow_le_rpow hsemi hr.le))
    (div_nonneg zero_le_one hr.le)
  change fracNorm Q α r w ≤ ((A * H) ^ r + (B * H) ^ r) ^ (1 / r) at hh
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ← add_mul, ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one hr.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one] at hh
  exact hh

lemma lower_moment_inverse_half_lt_top {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (t q : ℝ) (ht : 0 < t) (hq : 1 ≤ q)
    (hLower : 0 < lowerMoment a ha t q ht hq) :
    (lowerMoment a ha t q ht hq) ^ (-1 / 2 : ℝ) < ⊤ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, ENNReal.rpow_neg]
  exact ENNReal.inv_lt_top.mpr
    (ENNReal.rpow_pos_of_nonneg hLower (by norm_num))

lemma lower_eLpNorm_le_fracNorm {d : ℕ} {Q : Set (Vec d)} {α r : ℝ}
    (hr : 0 < r) (w : Vec d → ℝ) :
    eLpNorm w (ENNReal.ofReal r) (volume.restrict Q) ≤ fracNorm Q α r w := by
  have hh := ENNReal.rpow_le_rpow (x :=
    eLpNorm w (ENNReal.ofReal r) (volume.restrict Q) ^ r)
    (y := eLpNorm w (ENNReal.ofReal r) (volume.restrict Q) ^ r +
      fracSeminorm Q α r w ^ r) le_self_add (div_nonneg zero_le_one hr.le)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one] at hh
  exact hh


end CoarseDeGiorgi.LowerFractional
