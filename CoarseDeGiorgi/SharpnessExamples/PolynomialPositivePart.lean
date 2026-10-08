import CoarseDeGiorgi.SharpnessExamples.PolynomialField
import CoarseDeGiorgi.Statements.PositivePart
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The exterior radial profile stays above its interface value. -/
theorem polynomialProfile_ge_four {d : ℕ} {q t epsilon r : ℝ}
    (hd : 3 ≤ d) (hepsilon : 0 < epsilon)
    (hr : 2 * epsilon < r) : 4 ≤ polynomialProfile d q t epsilon r := by
  have hdR : 2 ≤ (d : ℝ) - 1 := by
    have hd' : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hperp : 0 < polynomialPerpendicular d q t epsilon :=
    polynomialPerpendicular_pos hepsilon
  have hcoef : 0 < 2 * polynomialPerpendicular d q t epsilon *
      (2 * epsilon) ^ (d - 1) / epsilon ^ 2 := by positivity
  have hfactor (z : ℝ) (hz : 2 * epsilon ≤ z) :
      0 ≤ Real.rpow z ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1) := by
    have hz0 : 0 < 2 * epsilon := by positivity
    have hzpos : 0 < z := lt_of_lt_of_le hz0 hz
    have hexp : 0 ≤ (d : ℝ) - 1 := by linarith
    have hmon := Real.rpow_le_rpow hz0.le hz hexp
    have hnat : (2 * epsilon) ^ (d - 1) = Real.rpow (2 * epsilon) ((d : ℝ) - 1) := by
      have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]
        norm_num
      calc
        (2 * epsilon) ^ (d - 1 : ℕ) =
            Real.rpow (2 * epsilon) ((d - 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast (2 * epsilon) (d - 1)).symm
        _ = Real.rpow (2 * epsilon) ((d : ℝ) - 1) := congrArg _ hcast
    change Real.rpow (2 * epsilon) ((d : ℝ) - 1) ≤
      Real.rpow z ((d : ℝ) - 1) at hmon
    change 0 ≤ Real.rpow z ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1 : ℕ)
    rw [hnat]
    exact sub_nonneg.mpr hmon
  have hnonneg : ∀ z ∈ Set.Icc (2 * epsilon) r,
      0 ≤ polynomialOuterDerivative d q t epsilon z := by
    intro z hz
    have hzle : 2 * epsilon ≤ z := hz.1
    have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hzle
    unfold polynomialOuterDerivative
    apply mul_nonneg (Real.rpow_nonneg hzpos.le _)
    have hsecond : 0 ≤ (2 / ((d : ℝ) - 1)) *
        (Real.rpow z ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1)) :=
      mul_nonneg (by positivity) (hfactor z hzle)
    linarith
  have hinterval : 0 ≤ ∫ z in (2 * epsilon)..r,
      polynomialOuterDerivative d q t epsilon z :=
    intervalIntegral.integral_nonneg hr.le hnonneg
  simp [polynomialProfile, not_le_of_gt hr]
  linarith

/-- On the unit cube, the positive part is exactly the truncated interior
quadratic profile; the radial continuation contributes no positive values. -/
theorem polynomialPositivePart_eq_inner {d : ℕ} [NeZero d]
    {q t epsilon : ℝ} (hd : 3 ≤ d)
    (hepsilon : 0 < epsilon) {x : Vec d}
    (hx : x ∈ originCube (d := d) 1) :
    positivePart (polynomialSolution d q t epsilon) x =
      max (1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2) 0 := by
  let r := Sharpness.transverseNorm x
  have hr0 : 0 ≤ r := Sharpness.lineRadius_nonneg x
  have hx0 : |x 0| < 1 / 2 := by
    rw [abs_lt]
    exact hx 0
  by_cases hinside : r ≤ 2 * epsilon
  · simp [positivePart, polynomialSolution, polynomialProfile, r, hinside]
  · have hr : 2 * epsilon < r := lt_of_not_ge hinside
    have hF := polynomialProfile_ge_four (q := q) (t := t) hd hepsilon hr
    have hxSq : (x 0) ^ 2 < 1 / 4 := by
      have habsSq : |x 0| ^ 2 < (1 / 2 : ℝ) ^ 2 :=
        (sq_lt_sq₀ (abs_nonneg (x 0)) (by norm_num)).2 hx0
      rw [sq_abs] at habsSq
      norm_num at habsSq
      exact habsSq
    have hactual : polynomialSolution d q t epsilon x < 0 := by
      dsimp [polynomialSolution]
      linarith
    have hinterior : 1 + (x 0) ^ 2 - r ^ 2 / epsilon ^ 2 < 0 := by
      have hratio : 2 < r / epsilon := (lt_div_iff₀ hepsilon).2 (by nlinarith)
      have hsq : 4 < (r / epsilon) ^ 2 := by nlinarith
      have heq : (r / epsilon) ^ 2 = r ^ 2 / epsilon ^ 2 := by field_simp
      rw [heq] at hsq
      linarith
    rw [positivePart, max_eq_right (le_of_lt hactual), max_eq_right (le_of_lt hinterior)]

/-- The positive part is bounded by the maximal axial height on the unit cube. -/
theorem polynomialPositivePart_le_five_quarters {d : ℕ} [NeZero d]
    {q t epsilon : ℝ} (hd : 3 ≤ d) (hepsilon : 0 < epsilon)
    {x : Vec d} (hx : x ∈ originCube (d := d) 1) :
    positivePart (polynomialSolution d q t epsilon) x ≤ 5 / 4 := by
  rw [polynomialPositivePart_eq_inner hd hepsilon hx]
  have hx0 : (x 0) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have habs : |x 0| < 1 / 2 := by
      rw [abs_lt]
      exact hx 0
    have hsq : |x 0| ^ 2 < (1 / 2 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (abs_nonneg (x 0)) (by norm_num)).2 habs
    rw [sq_abs] at hsq
    nlinarith
  have hr : 0 ≤ Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 := by positivity
  have hinner : 1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 ≤ 5 / 4 := by
    nlinarith
  exact max_le hinner (by norm_num)

/-- Every positive value of the construction lies in the radius `2ε` tube. -/
theorem polynomialPositivePart_pos_mem_responseCylinder {d : ℕ} [NeZero d]
    {q t epsilon : ℝ} (hd : 3 ≤ d) (hepsilon : 0 < epsilon)
    {x : Vec d} (hx : x ∈ originCube (d := d) 1)
    (hpos : 0 < positivePart (polynomialSolution d q t epsilon) x) :
    x ∈ responseCylinder epsilon := by
  rw [responseCylinder]
  have hformula := polynomialPositivePart_eq_inner (q := q) (t := t) hd hepsilon hx
  rw [hformula] at hpos
  have hinner : 1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 > 0 := by
    by_contra hn
    have hle : 1 + (x 0) ^ 2 - Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 ≤ 0 :=
      le_of_not_gt hn
    rw [max_eq_right hle] at hpos
    linarith
  have hx0 : (x 0) ^ 2 < 1 / 4 := by
    have habs : |x 0| < 1 / 2 := by
      rw [abs_lt]
      exact hx 0
    have hsq := (sq_lt_sq₀ (abs_nonneg (x 0)) (by norm_num)).2 habs
    rw [sq_abs] at hsq
    norm_num at hsq ⊢
    exact hsq
  have hr : 0 ≤ Sharpness.transverseNorm x := Sharpness.lineRadius_nonneg x
  have hratio : Sharpness.transverseNorm x ^ 2 / epsilon ^ 2 < 5 / 4 := by
    nlinarith
  have hε2 : 0 < epsilon ^ 2 := by positivity
  have hscaled : Sharpness.transverseNorm x ^ 2 < (5 / 4) * epsilon ^ 2 :=
    (div_lt_iff₀ hε2).1 hratio
  have hfour : (5 / 4) * epsilon ^ 2 < (2 * epsilon) ^ 2 := by nlinarith
  have hsq : Sharpness.transverseNorm x ^ 2 < (2 * epsilon) ^ 2 := hscaled.trans hfour
  exact (sq_lt_sq₀ hr (by positivity)).1 hsq

end

end CoarseDeGiorgi.SharpnessExamples
