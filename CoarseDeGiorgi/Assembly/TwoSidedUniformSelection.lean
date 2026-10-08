import CoarseDeGiorgi.Selection.SourceRepresentatives
import CoarseDeGiorgi.Assembly.HybridFractional
import CoarseDeGiorgi.Selection.TraceBounds
import CoarseDeGiorgi.Selection.SamplingMoment
import CoarseDeGiorgi.Weighted.UpperSpecNorm
import CoarseDeGiorgi.Assembly.LocalBoundedness

/-! The uniform selection theorem applied to the actual source shell. -/
namespace CoarseDeGiorgi.Assembly
open Homogenization MeasureTheory Set CoarseDeGiorgi.Localization
open scoped ENNReal BigOperators Matrix.Norms.L2Operator
noncomputable section

/-- Positive-dimensional source upper moments are nonzero. This removes the
infinite-L² endpoint without any additional coefficient hypothesis. -/
theorem two_sided_upper_moment_pos {d : ℕ} (hd : 0 < d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    0 < upperMoment a ha s p hs hp := by
  classical
  have hn (k : ℕ) (η : SimplexIndex d k) : 0 < ‖upperResponseOnCell k a ha η‖ :=
    Weighted.UpperResponseImpl.upperResponse_norm_pos
      (simplexCell_isOpenBoundedConvexDomain k η) (simplexCell_nonempty k η)
      (weightedCoeffOn_simplexCell k a ha η) hd
  have hc : 0 < (triangulation (d := d) 0).card := by
    rw [triangulation_card]
    simp only [zero_mul, pow_zero, mul_one]
    exact Nat.factorial_pos _
  have havg : 0 < upperCellAverage a ha 0 p := by
    unfold upperCellAverage
    apply div_pos
    · apply Finset.sum_pos
      · intro η _
        exact Real.rpow_pos_of_pos (hn 0 η) _
      · simpa only [Finset.attach_nonempty_iff] using Finset.card_pos.mp hc
    · exact_mod_cast hc
  have hsum : 0 < ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        ENNReal.ofReal (upperCellAverage a ha k p) ^ (1 / (2 * p)) := by
    apply lt_of_lt_of_le _ (ENNReal.le_tsum 0)
    simp only [Nat.cast_zero, zero_mul, neg_zero, Real.rpow_eq_pow, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr havg) ENNReal.ofReal_ne_top
  have hnorm : 0 < 1 - Real.rpow 3 (-s) := by
    have h := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3) (neg_neg_of_pos hs)
    simp only [Real.rpow_eq_pow]
    linarith only [h]
  unfold upperMoment
  exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _
    (mul_ne_zero (ENNReal.ofReal_pos.mpr hnorm).ne' hsum.ne'))

/-- The outer cube has volume at most one, so the lower exponent costs no constant. -/
theorem two_sided_lr_le_l2 {d : ℕ} {v : Vec d → ℝ} {q R : ℝ}
    (hq : 1 < q) (hR : R ≤ 1)
    (hv : AEStronglyMeasurable v (volume.restrict (originCube R))) :
    eLpNorm v (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) ≤
      eLpNorm v 2 (volume.restrict (originCube R)) := by
  have hr := theoremA_paramR_range hq
  change 1 < paramR q ∧ paramR q < 2 at hr
  have hpq : ENNReal.ofReal (paramR q) ≤ 2 := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hr.2.le
  have hexp : 0 ≤ 1 / (ENNReal.ofReal (paramR q)).toReal - 1 / (2 : ENNReal).toReal := by
    rw [ENNReal.toReal_ofReal (zero_lt_one.trans hr.1).le]
    norm_num only [ENNReal.toReal_ofNat]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (zero_lt_one.trans hr.1) hr.2.le)
  have hvol : (volume.restrict (originCube (d := d) R)) univ ≤ 1 := by
    rw [Measure.restrict_apply_univ]
    exact theoremA_cube_volume_le_one hR
  apply (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hv).trans
  simpa only [mul_one] using mul_le_mul'
    (le_refl (eLpNorm v 2 (volume.restrict (originCube R)))) (ENNReal.rpow_le_one hvol hexp)

end
end CoarseDeGiorgi.Assembly
