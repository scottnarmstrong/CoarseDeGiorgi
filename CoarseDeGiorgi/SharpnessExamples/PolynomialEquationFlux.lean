import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationGradient
import CoarseDeGiorgi.SharpnessExamples.PolynomialField

open Homogenization MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The coefficient multiplying the axial gradient in the explicit flux. -/
def polynomialAxialFactor (d : ℕ) (q t epsilon r : ℝ) : ℝ :=
  if r < 2 * epsilon then polynomialParallel d q t epsilon else 1

/-- The radial coefficient in the transverse part of the explicit flux. -/
def polynomialTransverseFactor (d : ℕ) (q t epsilon r : ℝ) : ℝ :=
  if r < 2 * epsilon then 2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2
  else polynomialOuterDerivative d q t epsilon r / r

/-- The candidate flux vector, written componentwise on the two regions. -/
def polynomialFlux (d : ℕ) [NeZero d] (q t epsilon : ℝ) (x : Vec d) : Vec d :=
  fun i => if i = (0 : Fin d) then
    2 * x (0 : Fin d) * polynomialAxialFactor d q t epsilon (Sharpness.transverseNorm x)
  else
    -polynomialTransverseFactor d q t epsilon (Sharpness.transverseNorm x) * x i

/-- Inside the cylinder the coefficient-weighted gradient has its elementary
quadratic form. -/
theorem polynomialCoefficient_mul_gradient_inside {d : ℕ} [NeZero d]
    (q t epsilon : ℝ) (he : 0 < epsilon) {x : Vec d}
    (hr : 0 < Sharpness.transverseNorm x)
    (hR : Sharpness.transverseNorm x < 2 * epsilon) (i : Fin d) :
    matVecMul (cylinderCoefficient epsilon (polynomialParallel d q t epsilon)
      (polynomialPerpendicular d q t epsilon) x)
      (polynomialGradient d q t epsilon x) i = polynomialFlux d q t epsilon x i := by
  have hgrad := polynomialSolution_smoothGrad_formula q t epsilon he hr (Or.inl hR) i
  have hc : x ∈ responseCylinder epsilon := by
    simpa [responseCylinder] using hR
  rw [cylinderCoefficient, ite_eq_left hc]
  change Matrix.mulVec (Matrix.diagonal (fun j : Fin d =>
      if j.val = 0 then polynomialParallel d q t epsilon
      else polynomialPerpendicular d q t epsilon))
      (smoothGrad (polynomialSolution d q t epsilon) x) i = _
  rw [Matrix.mulVec_diagonal]
  rw [hgrad]
  have hprof : deriv (polynomialProfile d q t epsilon)
      (Sharpness.transverseNorm x) = 2 * Sharpness.transverseNorm x / epsilon ^ 2 :=
    (polynomialProfile_hasDerivAt_inner q t epsilon _ he hR).deriv
  by_cases hi : i = 0
  · subst i
    simp [polynomialFlux, polynomialAxialFactor, hR]
    ring
  · rw [ite_eq_right hi, hprof]
    simp [hi, polynomialFlux, polynomialTransverseFactor, hR]
    field_simp [ne_of_gt hr, ne_of_gt he]

/-- Outside the cylinder the coefficient is the identity, and the flux is the
radial continuation. -/
theorem polynomialCoefficient_mul_gradient_outside {d : ℕ} [NeZero d]
    (q t epsilon : ℝ) (he : 0 < epsilon) {x : Vec d}
    (hr : 0 < Sharpness.transverseNorm x)
    (hR : 2 * epsilon < Sharpness.transverseNorm x) (i : Fin d) :
    matVecMul (cylinderCoefficient epsilon (polynomialParallel d q t epsilon)
      (polynomialPerpendicular d q t epsilon) x)
      (polynomialGradient d q t epsilon x) i = polynomialFlux d q t epsilon x i := by
  have hgrad := polynomialSolution_smoothGrad_formula q t epsilon he hr (Or.inr hR) i
  have hderiv : deriv (polynomialProfile d q t epsilon)
    (Sharpness.transverseNorm x) =
        polynomialOuterDerivative d q t epsilon (Sharpness.transverseNorm x) :=
    (polynomialProfile_hasDerivAt_outer q t epsilon _ he hR).deriv
  have hc : x ∉ responseCylinder epsilon := by
    simpa [responseCylinder] using not_lt_of_gt hR
  rw [cylinderCoefficient, ite_eq_right hc]
  change Matrix.mulVec (1 : Mat d) (smoothGrad (polynomialSolution d q t epsilon) x) i = _
  rw [Matrix.one_mulVec]
  rw [hgrad, hderiv]
  by_cases hi : i = 0
  · subst i
    simp [polynomialFlux, polynomialAxialFactor, not_lt_of_gt hR]
  · simp [hi, polynomialFlux, polynomialTransverseFactor, not_lt_of_gt hR]
    field_simp [ne_of_gt hr]

end

end CoarseDeGiorgi.SharpnessExamples
