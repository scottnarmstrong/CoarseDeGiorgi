import CoarseDeGiorgi.SharpnessExamples.PolynomialDefs
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition

/-! # The polynomial cylinder's conductivities on the active parameter range

These are the facts about the shared field `polynomialCoefficientFamily` that the moment bounds
use; they do not involve any response computation. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

/-- The inverse-moment exponent is strictly between zero and one. -/
theorem optimalPowers_hatT_mem_Ioo {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) : polynomialHatT d q t ∈ Set.Ioo 0 1 := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hdR : 0 < (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have htpos : 0 < polynomialHatT d q t := by
    unfold polynomialHatT
    positivity
  have hdecomp : paramTheta d p q s t =
      1 - (s + ((d : ℝ) - 1) / (2 * p)) - polynomialHatT d q t := by
    unfold paramTheta polynomialHatT
    ring
  have hsHat : 0 < s + ((d : ℝ) - 1) / (2 * p) := by positivity
  rw [hdecomp] at hθ
  exact ⟨htpos, by linarith⟩

/-- The conductivities satisfy exactly the phase hypotheses of
the cylinder bounds. -/
theorem optimalPowers_conductivities_bounds {d : ℕ} (hd : 3 ≤ d)
    {p q s t epsilon : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s)
    (ht : 0 < t) (hθ : 0 < paramTheta d p q s t)
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) :
    1 ≤ polynomialParallel d q t epsilon ∧
      0 < polynomialPerpendicular d q t epsilon ∧
      polynomialPerpendicular d q t epsilon ≤ 1 := by
  have hh := optimalPowers_hatT_mem_Ioo hd hp hq hs ht hθ
  have he1 : epsilon ≤ 1 := by linarith
  have hd1 : 1 ≤ (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hExp : 2 * polynomialHatT d q t - 2 ≤ 0 := by linarith [hh.2]
  have hOne : 1 ≤ Real.rpow epsilon (2 * polynomialHatT d q t - 2) := by
    simpa only [Real.rpow_eq_pow] using
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos he he1 hExp
  refine ⟨?_, ?_, ?_⟩
  · unfold polynomialParallel
    nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr hOne)]
  · unfold polynomialPerpendicular
    exact Real.rpow_pos_of_pos he _
  · unfold polynomialPerpendicular
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_one he.le he1 (by linarith [hh.1] : 0 ≤ 2 * polynomialHatT d q t)

/-- On the active interval the shared total field is literally the cylinder
field `cylinderCoefficient`. -/
theorem optimalPowers_family_eq_cylinder {d : ℕ} {q t epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) :
    polynomialCoefficientFamily d q t epsilon =
      cylinderCoefficient epsilon (polynomialParallel d q t epsilon)
        (polynomialPerpendicular d q t epsilon) := by
  have hcase : 0 < epsilon ∧ epsilon < 1 / 8 := ⟨he, he8⟩
  simp only [polynomialCoefficientFamily, ite_eq_left hcase]

/-- The unit cube carries the shared total coefficient for every ε. -/
theorem optimalPowers_family_weightedCoeffOn (d : ℕ) (hd : 3 ≤ d) (q t epsilon : ℝ) :
    IsWeightedCoeffOn (originCube (d := d) 1)
      (polynomialCoefficientFamily d q t epsilon) := by
  classical
  by_cases he : 0 < epsilon ∧ epsilon < 1 / 8
  · rw [optimalPowers_family_eq_cylinder he.1 he.2]
    apply cylinderCoefficient_weightedCoeffOn
    · rw [Assembly.ClassicalMomentsImpl.originCube_volume_one]
      simp
    · unfold polynomialParallel
      have hd : 0 < (d : ℝ) - 1 := by
        have hd3 : 3 ≤ d := hd
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd3
        linarith
      exact mul_pos hd (Real.rpow_pos_of_pos he.1 _)
    · unfold polynomialPerpendicular
      exact Real.rpow_pos_of_pos he.1 _
  · rw [polynomialCoefficientFamily]
    simp only [ite_eq_right he]
    refine ⟨aestronglyMeasurable_const, ?_, ?_, ?_⟩
    · filter_upwards with x
      exact Matrix.PosDef.one
    · exact integrableOn_const (by
        rw [Assembly.ClassicalMomentsImpl.originCube_volume_one]; simp)
    · simpa using (integrableOn_const (by
        rw [Assembly.ClassicalMomentsImpl.originCube_volume_one]; simp) :
        IntegrableOn (fun _ : Vec d => (1 : Mat d).trace) (originCube 1))

end CoarseDeGiorgi.SharpnessExamples
