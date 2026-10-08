import CoarseDeGiorgi.Assembly.ClassicalMomentsCellBounds
import Mathlib.Analysis.SpecificLimits.Basic

namespace CoarseDeGiorgi.Assembly.ClassicalMomentsImpl

open Homogenization MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

/-- The source geometric weights have exactly unit mass after normalization. -/
theorem geometric_normalization {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s)))) = 1 := by
  let r := Real.rpow 3 (-s)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  have hw (k : ℕ) : Real.rpow 3 (-((k : ℝ) * s)) = r ^ k := by
    rw [show -((k : ℝ) * s) = -s * k by ring]
    change (3 : ℝ) ^ (-s * (k : ℝ)) = r ^ k
    exact Real.rpow_mul_natCast (by norm_num) (-s) k
  simp_rw [hw, ENNReal.ofReal_pow hr0]
  rw [ENNReal.tsum_geometric]
  have ha : ENNReal.ofReal (1 - r) = 1 - ENNReal.ofReal r := by
    rw [ENNReal.ofReal_sub 1 hr0]
    simp
  change ENNReal.ofReal (1 - r) * _ = 1
  rw [← ha]
  exact ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr hr1)).ne'
    ENNReal.ofReal_ne_top

/-- Uniform level bounds pass through the normalized half-power series. -/
theorem normalized_series_le {p s M : ℝ} (hp : 0 < p) (hs : 0 < s)
    (b : ℕ → ℝ) (hb : ∀ k, b k ≤ M) :
    ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (b k)).rpow (1 / (2 * p))) ≤
      (ENNReal.ofReal M).rpow (1 / (2 * p)) := by
  calc
    _ ≤ ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
        (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
          (ENNReal.ofReal M).rpow (1 / (2 * p))) := by
      apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      intro k
      exact mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hb k))
        (by positivity)) _
    _ = (ENNReal.ofReal M).rpow (1 / (2 * p)) := by
      rw [ENNReal.tsum_mul_right, ← mul_assoc, geometric_normalization hs, one_mul]

theorem half_power_sq (M : ENNReal) {p : ℝ} (hp : 0 < p) :
    (M.rpow (1 / (2 * p))) ^ 2 = M.rpow (1 / p) := by
  change (M ^ (1 / (2 * p) : ℝ)) ^ 2 = M ^ (1 / p : ℝ)
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  norm_num
  field_simp

/-- The upper response moment is bounded by the classical Lp norm with constant one. -/
theorem upperMoment_le_classical {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {p s : ℝ} (hp : 1 ≤ p) (hs : 0 < s)
    (hLp : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (originCube 1)) < ⊤) :
    upperMoment a ha s p hs hp ≤
      eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hb := normalized_series_le hp0 hs (fun k => upperCellAverage a ha k p)
    (upperCellAverage_bound a ha hp hLp)
  obtain ⟨_, hi⟩ := classical_integrability hp ha.1 hLp
  rw [classical_eLpNorm_eq hp0 ha.1 hi]
  exact (pow_le_pow_left' hb 2).trans_eq (half_power_sq _ hp0)


end CoarseDeGiorgi.Assembly.ClassicalMomentsImpl
