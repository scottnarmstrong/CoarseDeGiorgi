import CoarseDeGiorgi.SharpnessExamples.CylinderResponseDefs
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.SmoothGrad
import CoarseDeGiorgi.Sharpness.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Homogenization MeasureTheory

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The inverse-moment exponent in the polynomial cylinder. -/
def polynomialHatT (d : ℕ) (q t : ℝ) : ℝ := t + ((d : ℝ) - 1) / (2 * q)

/-- The small transverse conductivity from Proposition `p.sharpness.polynomial`. -/
def polynomialPerpendicular (d : ℕ) (q t epsilon : ℝ) : ℝ :=
  Real.rpow epsilon (2 * polynomialHatT d q t)

/-- The large axial conductivity from Proposition `p.sharpness.polynomial`. -/
def polynomialParallel (d : ℕ) (q t epsilon : ℝ) : ℝ :=
  ((d : ℝ) - 1) * Real.rpow epsilon (2 * polynomialHatT d q t - 2)

/-- The radial derivative used outside the thin cylinder. -/
def polynomialOuterDerivative (d : ℕ) (q t epsilon r : ℝ) : ℝ :=
  Real.rpow r (2 - (d : ℝ)) *
    (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) / epsilon ^ 2 +
      (2 / ((d : ℝ) - 1)) *
        (Real.rpow r ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1))
    )

/-- The matched radial profile in the proof of Proposition `p.sharpness.polynomial`. -/
def polynomialProfile (d : ℕ) (q t epsilon r : ℝ) : ℝ :=
  if r ≤ 2 * epsilon then r ^ 2 / epsilon ^ 2 else
    4 + ∫ z in (2 * epsilon)..r, polynomialOuterDerivative d q t epsilon z

/-- The explicit sign-changing solution in Proposition `p.sharpness.polynomial`. -/
def polynomialSolution (d : ℕ) [NeZero d] (q t epsilon : ℝ) (x : Vec d) : ℝ :=
  1 + (x 0) ^ 2 - polynomialProfile d q t epsilon (Sharpness.transverseNorm x)

/-- The weak gradient chosen for the explicit polynomial profile. -/
def polynomialGradient (d : ℕ) [NeZero d] (q t epsilon : ℝ) : Vec d → Vec d :=
  smoothGrad (polynomialSolution d q t epsilon)

/-- The cylinder field, with the identity continuation outside the parameter
interval used by the existential statement `sharpness_polynomial`. -/
def polynomialCoefficientFamily (d : ℕ) (q t epsilon : ℝ) : CoeffField d := by
  classical
  exact if 0 < epsilon ∧ epsilon < 1 / 8 then
    cylinderCoefficient epsilon (polynomialParallel d q t epsilon)
      (polynomialPerpendicular d q t epsilon)
  else fun _ => 1

end

end CoarseDeGiorgi.SharpnessExamples
