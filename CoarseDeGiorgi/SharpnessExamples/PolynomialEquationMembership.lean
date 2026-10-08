import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationRegularity
import CoarseDeGiorgi.Sharpness.LineEquation.LineBasics
import CoarseDeGiorgi.SharpnessExamples.PolynomialField
import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry
import CoarseDeGiorgi.Foundations.Euclid.Basic
import CoarseDeGiorgi.Weighted.Lipschitz

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem eNorm2_transversePart_le {d : ℕ} (x : Vec d) :
    Foundations.Euclid.eNorm2 (Sharpness.transversePart x) ≤
      Foundations.Euclid.eNorm2 x := by
  have hsquare : vecNormSq (Sharpness.transversePart x) ≤ vecNormSq x := by
    unfold vecNormSq
    apply Finset.sum_le_sum
    intro i hi
    by_cases hiz : i.val = 0
    · simp [Sharpness.transversePart, hiz]
      simpa only [pow_two] using sq_nonneg (x i)
    · simp [Sharpness.transversePart, hiz]
  exact Real.sqrt_le_sqrt hsquare

private theorem transversePart_sub {d : ℕ} (x y : Vec d) :
    Sharpness.transversePart x - Sharpness.transversePart y =
      Sharpness.transversePart (x - y) := by
  funext i
  by_cases hi : i.val = 0 <;> simp [Sharpness.transversePart, hi]

/-- The transverse radius is Lipschitz with respect to the ambient product
metric, with the dimension conversion from the project sup norm. -/
theorem transverseNorm_dist_le {d : ℕ} (x y : Vec d) :
    |Sharpness.transverseNorm x - Sharpness.transverseNorm y| ≤
      Real.sqrt (d : ℝ) * dist x y := by
  have hnorm : |Sharpness.transverseNorm x - Sharpness.transverseNorm y| ≤
      Foundations.Euclid.eNorm2 (Sharpness.transversePart x -
        Sharpness.transversePart y) := by
    change |Foundations.Euclid.eNorm2 (Sharpness.transversePart x) -
      Foundations.Euclid.eNorm2 (Sharpness.transversePart y)| ≤
      Foundations.Euclid.eNorm2 (Sharpness.transversePart x -
        Sharpness.transversePart y)
    rw [Foundations.Euclid.eNorm2_eq_norm_toLp,
      Foundations.Euclid.eNorm2_eq_norm_toLp,
      Foundations.Euclid.eNorm2_eq_norm_toLp]
    have h := abs_norm_sub_norm_le
      (WithLp.toLp 2 (Sharpness.transversePart x))
      (WithLp.toLp 2 (Sharpness.transversePart y))
    simpa only [WithLp.toLp_sub] using h
  have hproj := transversePart_sub x y
  calc
    _ ≤ Foundations.Euclid.eNorm2 (Sharpness.transversePart x -
        Sharpness.transversePart y) := hnorm
    _ = Foundations.Euclid.eNorm2 (Sharpness.transversePart (x - y)) := by rw [hproj]
    _ ≤ Foundations.Euclid.eNorm2 (x - y) := eNorm2_transversePart_le _
    _ ≤ Real.sqrt (d : ℝ) * ‖x - y‖ :=
      Foundations.Euclid.eNorm2_le_sqrt_mul_norm _
    _ = Real.sqrt (d : ℝ) * dist x y := by rw [dist_eq_norm]

/-- On the unit cube, the explicit solution is Lipschitz, despite the jump in
its radial derivative at the coefficient interface. -/
theorem polynomialSolution_lipschitzOn {d : ℕ} [NeZero d]
    {q t epsilon : ℝ} (hd : 3 ≤ d) (he : 0 < epsilon) (he8 : epsilon < 1 / 8) :
    ∃ L : ℝ≥0, LipschitzOnWith L (polynomialSolution d q t epsilon)
      (originCube (d := d) 1) := by
  have hradUpper {x : Vec d} (hx : x ∈ originCube (d := d) 1) :
      Sharpness.transverseNorm x ≤ (d : ℝ) := by
    have h := Sharpness.transverseNorm_le_sqrt_d_div_two hx
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
    have hsquare : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have hsqrt := Real.sqrt_le_sqrt hsquare
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_trans (by norm_num) hdR)] at hsqrt
    nlinarith
  have hR : 2 * epsilon ≤ (d : ℝ) := by
    have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK, hprof⟩ :=
    polynomialProfile_lipschitzOn (d := d) q t epsilon (d : ℝ) he hR
  have hLnonneg : 0 ≤ 1 + K * Real.sqrt (d : ℝ) := by positivity
  let L : ℝ≥0 := ⟨1 + K * Real.sqrt (d : ℝ), hLnonneg⟩
  refine ⟨L, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Real.dist_eq]
  change |polynomialSolution d q t epsilon x -
    polynomialSolution d q t epsilon y| ≤ (L : ℝ) * ‖x - y‖
  have hxcoord : |x 0| < 1 / 2 := by
    rw [abs_lt]
    exact hx 0
  have hycoord : |y 0| < 1 / 2 := by
    rw [abs_lt]
    exact hy 0
  have hcoord : |x 0 - y 0| ≤ dist x y := by
    have h := norm_le_pi_norm (x - y) (0 : Fin d)
    simpa [dist_eq_norm, Real.norm_eq_abs] using h
  have hsum : |x 0 + y 0| ≤ 1 := by
    calc
      |x 0 + y 0| ≤ |x 0| + |y 0| := abs_add_le _ _
      _ ≤ 1 := by linarith [abs_nonneg (x 0), abs_nonneg (y 0)]
  have haxial : |(x 0) ^ 2 - (y 0) ^ 2| ≤ dist x y := by
    have hfactor : (x 0) ^ 2 - (y 0) ^ 2 = (x 0 - y 0) * (x 0 + y 0) := by ring
    rw [hfactor, abs_mul]
    calc
      |x 0 - y 0| * |x 0 + y 0| ≤ dist x y * 1 :=
        mul_le_mul hcoord hsum (abs_nonneg _) (dist_nonneg)
      _ = dist x y := by ring
  have hrx : Sharpness.transverseNorm x ∈ Icc (0 : ℝ) (d : ℝ) :=
    ⟨Sharpness.lineRadius_nonneg x, hradUpper hx⟩
  have hry : Sharpness.transverseNorm y ∈ Icc (0 : ℝ) (d : ℝ) :=
    ⟨Sharpness.lineRadius_nonneg y, hradUpper hy⟩
  have hrad : |Sharpness.transverseNorm x - Sharpness.transverseNorm y| ≤
      Real.sqrt (d : ℝ) * dist x y := transverseNorm_dist_le x y
  have hprofxy := hprof (Sharpness.transverseNorm x) hrx
    (Sharpness.transverseNorm y) hry
  have hprofile :
      |polynomialProfile d q t epsilon (Sharpness.transverseNorm x) -
        polynomialProfile d q t epsilon (Sharpness.transverseNorm y)| ≤
        (K * Real.sqrt (d : ℝ)) * dist x y := by
    calc
      _ ≤ K * |Sharpness.transverseNorm x - Sharpness.transverseNorm y| := hprofxy
      _ ≤ K * (Real.sqrt (d : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left hrad hK
      _ = (K * Real.sqrt (d : ℝ)) * dist x y := by ring
  have hsol :
      |polynomialSolution d q t epsilon x - polynomialSolution d q t epsilon y| ≤
        (1 + K * Real.sqrt (d : ℝ)) * dist x y := by
    change |((1 + (x 0) ^ 2 -
        polynomialProfile d q t epsilon (Sharpness.transverseNorm x)) -
      (1 + (y 0) ^ 2 -
        polynomialProfile d q t epsilon (Sharpness.transverseNorm y)))| ≤ _
    have hsplit :
        ((1 + (x 0) ^ 2 - polynomialProfile d q t epsilon (Sharpness.transverseNorm x)) -
          (1 + (y 0) ^ 2 - polynomialProfile d q t epsilon (Sharpness.transverseNorm y))) =
          ((x 0) ^ 2 - (y 0) ^ 2) -
            (polynomialProfile d q t epsilon (Sharpness.transverseNorm x) -
              polynomialProfile d q t epsilon (Sharpness.transverseNorm y)) := by ring
    rw [hsplit]
    calc
      |((x 0) ^ 2 - (y 0) ^ 2) -
          (polynomialProfile d q t epsilon (Sharpness.transverseNorm x) -
            polynomialProfile d q t epsilon (Sharpness.transverseNorm y))|
          ≤ |(x 0) ^ 2 - (y 0) ^ 2| +
            |polynomialProfile d q t epsilon (Sharpness.transverseNorm x) -
              polynomialProfile d q t epsilon (Sharpness.transverseNorm y)| := by
            calc
              _ = |((x 0) ^ 2 - (y 0) ^ 2) +
                  - (polynomialProfile d q t epsilon (Sharpness.transverseNorm x) -
                    polynomialProfile d q t epsilon (Sharpness.transverseNorm y))| := by ring_nf
              _ ≤ |(x 0) ^ 2 - (y 0) ^ 2| +
                  |-(polynomialProfile d q t epsilon (Sharpness.transverseNorm x) -
                    polynomialProfile d q t epsilon (Sharpness.transverseNorm y))| :=
                    abs_add_le _ _
              _ = _ := by rw [abs_neg]
      _ ≤ dist x y + (K * Real.sqrt (d : ℝ)) * dist x y := add_le_add haxial hprofile
      _ = (1 + K * Real.sqrt (d : ℝ)) * dist x y := by ring
  rw [show (L : ℝ) = 1 + K * Real.sqrt (d : ℝ) by rfl]
  simpa only [dist_eq_norm] using hsol

/-- Every active polynomial solution belongs to the weighted Sobolev space on
the unit cube. -/
theorem polynomialSolution_memH1a {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) :
    MemH1a (polynomialCoefficientFamily d q t epsilon)
      (originCube (d := d) 1) (polynomialSolution d q t epsilon)
      (polynomialGradient d q t epsilon) := by
  obtain ⟨hV, hne⟩ := Sharpness.originCube_one_domain (d := d)
  have ha : IsWeightedCoeffOn (originCube (d := d) 1)
      (polynomialCoefficientFamily d q t epsilon) :=
    polynomialCoefficientFamily_weightedCoeffOn (by omega) q t epsilon
  obtain ⟨L, hLip⟩ := polynomialSolution_lipschitzOn hd he he8
  exact Weighted.memH1a_of_lipschitzOn hV hne ha hLip (by rfl)

end

end CoarseDeGiorgi.SharpnessExamples
