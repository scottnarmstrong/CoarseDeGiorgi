import CoarseDeGiorgi.SharpnessExamples.PolynomialDefs

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The exterior radial derivative is continuous on a compact interval away
from the singular radius zero. -/
theorem polynomialOuterDerivative_continuousOn {d : ℕ} (q t epsilon : ℝ)
    {R S : ℝ} (hR : 0 < R) (_hRS : R ≤ S) :
    ContinuousOn (polynomialOuterDerivative d q t epsilon) (Icc R S) := by
  have hbase (p : ℝ) : ContinuousOn (fun r : ℝ => Real.rpow r p) (Icc R S) := by
    intro r hr
    exact (Real.continuousAt_rpow_const r p (Or.inl (ne_of_gt (hR.trans_le hr.1)))).continuousWithinAt
  have hNat : ContinuousOn (fun r : ℝ => r ^ (d - 1)) (Icc R S) := by
    fun_prop
  have hA : ContinuousOn (fun _ : ℝ =>
      2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
        epsilon ^ 2) (Icc R S) := continuousOn_const
  have hB : ContinuousOn (fun r : ℝ =>
      2 / ((d : ℝ) - 1) *
        (Real.rpow r ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1)))
      (Icc R S) := by
    exact continuousOn_const.mul ((hbase _).sub continuousOn_const)
  have hsum : ContinuousOn (fun r : ℝ =>
      2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
        epsilon ^ 2 +
      2 / ((d : ℝ) - 1) *
        (Real.rpow r ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1)))
      (Icc R S) := hA.add hB
  change ContinuousOn (fun r : ℝ => Real.rpow r (2 - (d : ℝ)) *
    (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
      epsilon ^ 2 +
    2 / ((d : ℝ) - 1) *
      (Real.rpow r ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1)))) (Icc R S)
  exact (hbase _).mul hsum

private theorem polynomialProfile_outer_repr {d : ℕ} (q t epsilon : ℝ)
    (he : 0 < epsilon) {r : ℝ} (hr : 2 * epsilon ≤ r) :
    polynomialProfile d q t epsilon r =
      4 + ∫ z in (2 * epsilon)..r, polynomialOuterDerivative d q t epsilon z := by
  by_cases hEq : r = 2 * epsilon
  · subst r
    simp [polynomialProfile]
    field_simp [he.ne']
    ring
  · have hgt : 2 * epsilon < r := lt_of_le_of_ne hr (Ne.symm hEq)
    simp [polynomialProfile, not_le_of_gt hgt]

/-- The explicit radial profile is Lipschitz on every bounded nonnegative
radius interval. -/
theorem polynomialProfile_lipschitzOn {d : ℕ} (q t epsilon S : ℝ)
    (he : 0 < epsilon) (hR : 2 * epsilon ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (0 : ℝ) S, ∀ y ∈ Icc (0 : ℝ) S,
      |polynomialProfile d q t epsilon x - polynomialProfile d q t epsilon y|
        ≤ K * |x - y| := by
  let R := 2 * epsilon
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRS : R ≤ S := by simpa [R] using hR
  have hDcont := polynomialOuterDerivative_continuousOn (d := d) q t epsilon
    (R := R) (S := S) hRpos hRS
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hDcont
  let B := max 0 C
  have hB : 0 ≤ B := le_max_left _ _
  have hDbound : ∀ z ∈ Icc R S,
      |polynomialOuterDerivative d q t epsilon z| ≤ B := by
    intro z hz
    rw [← Real.norm_eq_abs]
    exact (hC z hz).trans (le_max_right _ _)
  let K := max (4 / epsilon) B
  have hK : 0 ≤ K := le_max_of_le_right hB
  have hordered : ∀ x y : ℝ, x ∈ Icc (0 : ℝ) S → y ∈ Icc (0 : ℝ) S →
      x ≤ y → |polynomialProfile d q t epsilon x - polynomialProfile d q t epsilon y|
        ≤ K * |x - y| := by
    intro x y hx hy hxy
    have hx0 := hx.1
    have hyS := hy.2
    have hKeps : 4 / epsilon ≤ K := le_max_left _ _
    have hKB : B ≤ K := le_max_right _ _
    by_cases hyR : y ≤ R
    · have hxR : x ≤ R := hxy.trans hyR
      have hPx : polynomialProfile d q t epsilon x = x ^ 2 / epsilon ^ 2 := by
        simp [polynomialProfile, R, hxR]
      have hPy : polynomialProfile d q t epsilon y = y ^ 2 / epsilon ^ 2 := by
        simp [polynomialProfile, R, hyR]
      have hsquares : x ^ 2 ≤ y ^ 2 := by nlinarith
      rw [hPx, hPy]
      rw [abs_of_nonpos (sub_nonpos.mpr
        (div_le_div_of_nonneg_right hsquares (sq_nonneg epsilon)))]
      have hfactor : y ^ 2 / epsilon ^ 2 - x ^ 2 / epsilon ^ 2 =
          (y - x) * ((y + x) / epsilon ^ 2) := by field_simp; ring
      have hneg : -(x ^ 2 / epsilon ^ 2 - y ^ 2 / epsilon ^ 2) =
          y ^ 2 / epsilon ^ 2 - x ^ 2 / epsilon ^ 2 := by ring
      rw [hneg, hfactor]
      have hsum : x + y ≤ 2 * R := by linarith
      have hcoef : (y + x) / epsilon ^ 2 ≤ 4 / epsilon := by
        rw [show R = 2 * epsilon by rfl] at hsum
        rw [div_le_iff₀ (by positivity : 0 < epsilon ^ 2)]
        have heq : (4 / epsilon) * epsilon ^ 2 = 4 * epsilon := by
          field_simp [he.ne']
        rw [heq]
        linarith
      have hdiff : 0 ≤ y - x := sub_nonneg.mpr hxy
      calc
        (y - x) * ((y + x) / epsilon ^ 2) ≤ (y - x) * (4 / epsilon) :=
          mul_le_mul_of_nonneg_left hcoef hdiff
        _ ≤ K * |x - y| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
          nlinarith [mul_le_mul_of_nonneg_left hKeps hdiff]
    · have hyR' : R ≤ y := le_of_not_ge hyR
      have hI_Ry : IntervalIntegrable (polynomialOuterDerivative d q t epsilon)
          volume R y := by
        have hDc : ContinuousOn (polynomialOuterDerivative d q t epsilon) (uIcc R y) := by
          rw [uIcc_of_le hyR']
          exact hDcont.mono (Icc_subset_Icc le_rfl hyS)
        exact hDc.intervalIntegrable (μ := volume)
      by_cases hxR : R ≤ x
      · have hI_Rx : IntervalIntegrable (polynomialOuterDerivative d q t epsilon)
            volume R x := by
          have hDc : ContinuousOn (polynomialOuterDerivative d q t epsilon) (uIcc R x) := by
            rw [uIcc_of_le hxR]
            exact hDcont.mono (Icc_subset_Icc le_rfl hx.2)
          exact hDc.intervalIntegrable (μ := volume)
        have hPx := polynomialProfile_outer_repr (d := d) q t epsilon he hxR
        have hPy := polynomialProfile_outer_repr (d := d) q t epsilon he hyR'
        have hdiff := intervalIntegral.integral_interval_sub_left hI_Ry hI_Rx
        have hI : ‖∫ z in x..y, polynomialOuterDerivative d q t epsilon z‖ ≤
            B * |y - x| := by
          exact intervalIntegral.norm_integral_le_of_norm_le_const fun z hz => by
            rw [uIoc_of_le hxy] at hz
            exact hDbound z ⟨le_trans hxR hz.1.le, le_trans hz.2 hyS⟩
        rw [hPx, hPy]
        have hrewrite : (4 + ∫ z in R..x, polynomialOuterDerivative d q t epsilon z) -
            (4 + ∫ z in R..y, polynomialOuterDerivative d q t epsilon z) =
            -(∫ z in x..y, polynomialOuterDerivative d q t epsilon z) := by
          rw [← hdiff]
          ring
        rw [hrewrite, abs_neg, ← Real.norm_eq_abs]
        rw [abs_sub_comm y x] at hI
        exact hI.trans (mul_le_mul_of_nonneg_right hKB (abs_nonneg (x - y)))
      · have hxR' : x ≤ R := le_of_not_ge hxR
        have hI : ‖∫ z in R..y, polynomialOuterDerivative d q t epsilon z‖ ≤
          B * |y - R| := by
          exact intervalIntegral.norm_integral_le_of_norm_le_const fun z hz => by
            rw [uIoc_of_le hyR'] at hz
            exact hDbound z ⟨hz.1.le, le_trans hz.2 hyS⟩
        have hPy := polynomialProfile_outer_repr (d := d) q t epsilon he hyR'
        have hPx : polynomialProfile d q t epsilon x = x ^ 2 / epsilon ^ 2 := by
          simp [polynomialProfile, R, hxR']
        have hinner : |x ^ 2 / epsilon ^ 2 - 4| ≤
            (4 / epsilon) * (R - x) := by
          have hxRtwo : x ≤ 2 * epsilon := by simpa [R] using hxR'
          have hsquare : x ^ 2 ≤ (2 * epsilon) ^ 2 :=
            (sq_le_sq₀ (by positivity : 0 ≤ x) (by positivity : 0 ≤ 2 * epsilon)).2 hxRtwo
          have hxSq : x ^ 2 / epsilon ^ 2 ≤ 4 := by
            apply (div_le_iff₀ (by positivity : 0 < epsilon ^ 2)).2
            nlinarith
          have hcoef : (2 * epsilon + x) / epsilon ^ 2 ≤ 4 / epsilon := by
            rw [div_le_iff₀ (by positivity : 0 < epsilon ^ 2)]
            have hsum : 2 * epsilon + x ≤ 4 * epsilon := by linarith
            have heq : (4 / epsilon) * epsilon ^ 2 = 4 * epsilon := by
              field_simp [he.ne']
            rw [heq]
            linarith
          have hfactor : 4 - x ^ 2 / epsilon ^ 2 =
              (2 * epsilon - x) * ((2 * epsilon + x) / epsilon ^ 2) := by
            field_simp [he.ne']
            ring
          have hrewriteR : R - x = 2 * epsilon - x := by rfl
          have hneg : -(x ^ 2 / epsilon ^ 2 - 4) = 4 - x ^ 2 / epsilon ^ 2 := by ring
          rw [abs_of_nonpos (sub_nonpos.mpr hxSq), hneg, hfactor, hrewriteR]
          calc
            _ ≤ (2 * epsilon - x) * (4 / epsilon) :=
              mul_le_mul_of_nonneg_left hcoef (sub_nonneg.mpr hxRtwo)
            _ = (4 / epsilon) * (2 * epsilon - x) := by ring
        have h1 : |polynomialProfile d q t epsilon y - 4| ≤ K * (y - R) := by
          rw [hPy]
          have hrewrite : (4 + ∫ z in (2 * epsilon)..y,
              polynomialOuterDerivative d q t epsilon z) - 4 =
              ∫ z in R..y, polynomialOuterDerivative d q t epsilon z := by
            simp [R]
          rw [hrewrite, ← Real.norm_eq_abs]
          have hnonneg : 0 ≤ y - R := sub_nonneg.mpr hyR'
          have hI' := hI
          rw [abs_of_nonneg hnonneg] at hI'
          exact hI'.trans (mul_le_mul_of_nonneg_right hKB hnonneg)
        have h2 : |4 - polynomialProfile d q t epsilon x| ≤ K * (R - x) := by
          rw [hPx]
          have hsymm : |4 - x ^ 2 / epsilon ^ 2| = |x ^ 2 / epsilon ^ 2 - 4| := abs_sub_comm _ _
          rw [hsymm]
          exact hinner.trans (mul_le_mul_of_nonneg_right hKeps (by linarith))
        have htri : |polynomialProfile d q t epsilon x - polynomialProfile d q t epsilon y| ≤
            |polynomialProfile d q t epsilon x - 4| +
              |4 - polynomialProfile d q t epsilon y| := by
          calc
            _ = |(polynomialProfile d q t epsilon x - 4) +
                (4 - polynomialProfile d q t epsilon y)| := by congr 1; ring
            _ ≤ _ := abs_add_le _ _
        have hdist : (R - x) + (y - R) = |x - y| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
          ring
        have h1' : |4 - polynomialProfile d q t epsilon y| ≤ K * (y - R) := by
          rw [abs_sub_comm]
          exact h1
        have h2' : |polynomialProfile d q t epsilon x - 4| ≤ K * (R - x) := by
          rw [abs_sub_comm]
          exact h2
        calc
          |polynomialProfile d q t epsilon x - polynomialProfile d q t epsilon y|
              ≤ K * (R - x) + K * (y - R) := htri.trans (add_le_add h2' h1')
          _ = K * |x - y| := by rw [← mul_add, hdist]
  refine ⟨K, hK, ?_⟩
  intro x hx y hy
  by_cases hxy : x ≤ y
  · exact hordered x y hx hy hxy
  · have h := hordered y x hy hx (le_of_not_ge hxy)
    simpa [abs_sub_comm] using h

end

end CoarseDeGiorgi.SharpnessExamples
