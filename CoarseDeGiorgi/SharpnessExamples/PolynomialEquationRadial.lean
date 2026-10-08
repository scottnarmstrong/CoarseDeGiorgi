import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationFlux
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Homogenization MeasureTheory Set Filter Topology

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem polynomial_rpow_nat {d : ℕ} (hd : 1 ≤ d) (r : ℝ) :
    Real.rpow r ((d : ℝ) - 1) = r ^ (d - 1) := by
  have hcast : (d : ℝ) - 1 = ((d - 1 : ℕ) : ℝ) := by
    norm_cast
  calc
    Real.rpow r ((d : ℝ) - 1) = Real.rpow r ((d - 1 : ℕ) : ℝ) := by rw [hcast]
    _ = r ^ (d - 1) := Real.rpow_natCast r (d - 1)

private theorem polynomial_rpow_product {d : ℕ} (_hd : 1 ≤ d) {r : ℝ}
    (hr : 0 < r) : Real.rpow r (2 - (d : ℝ)) *
      Real.rpow r ((d : ℝ) - 1) = r := by
  calc
    Real.rpow r (2 - (d : ℝ)) * Real.rpow r ((d : ℝ) - 1) =
        Real.rpow r ((2 - (d : ℝ)) + ((d : ℝ) - 1)) :=
      (Real.rpow_add hr _ _).symm
    _ = r := by
      have hexp : 2 - (d : ℝ) + ((d : ℝ) - 1) = 1 := by ring
      rw [hexp]
      simp

/-- A useful simplified formula for the exterior radial flux. -/
theorem polynomialOuterDerivative_eq_linear_rpow {d : ℕ} (hd : 3 ≤ d)
    (q t epsilon r : ℝ) (hr : 0 < r) :
    polynomialOuterDerivative d q t epsilon r =
      (2 / ((d : ℝ) - 1)) * r +
        (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
            epsilon ^ 2 -
          (2 / ((d : ℝ) - 1)) * (2 * epsilon) ^ (d - 1)) *
          Real.rpow r (2 - (d : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  let A : ℝ := 2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
    epsilon ^ 2
  let B : ℝ := 2 / ((d : ℝ) - 1)
  unfold polynomialOuterDerivative
  have hpow := polynomial_rpow_product hd1 hr
  calc
    Real.rpow r (2 - (d : ℝ)) *
        (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2 +
         2 / ((d : ℝ) - 1) *
          (Real.rpow r ((d : ℝ) - 1) - (2 * epsilon) ^ (d - 1))) =
      (2 * polynomialPerpendicular d q t epsilon * (2 * epsilon) ^ (d - 1) /
          epsilon ^ 2) * Real.rpow r (2 - (d : ℝ)) +
        (2 / ((d : ℝ) - 1)) *
          (Real.rpow r (2 - (d : ℝ)) * Real.rpow r ((d : ℝ) - 1) -
            (2 * epsilon) ^ (d - 1) * Real.rpow r (2 - (d : ℝ))) := by ring
    _ = _ := by rw [hpow]; ring

/-- The radial flux agrees with the interior transverse flux at the interface. -/
theorem polynomialTransverseFactor_interface {d : ℕ} (hd : 3 ≤ d)
    {q t epsilon : ℝ} (he : 0 < epsilon) :
    polynomialOuterDerivative d q t epsilon (2 * epsilon) / (2 * epsilon) =
      2 * polynomialPerpendicular d q t epsilon / epsilon ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hR : 0 < (2 * epsilon : ℝ) := by positivity
  have hprofile := polynomialOuterDerivative_eq_linear_rpow hd q t epsilon (2 * epsilon) hR
  rw [hprofile]
  have hdne : (d : ℝ) - 1 ≠ 0 := by
    have h : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hpower : Real.rpow (2 * epsilon) (2 - (d : ℝ)) *
      Real.rpow (2 * epsilon) ((d : ℝ) - 1) = 2 * epsilon := by
    exact polynomial_rpow_product hd1 hR
  have hpower' : Real.rpow (2 * epsilon) (2 - (d : ℝ)) =
      (2 * epsilon) / (2 * epsilon) ^ (d - 1) := by
    have hnat := polynomial_rpow_nat hd1 (2 * epsilon)
    rw [← hnat]
    field_simp [ne_of_gt hR]
    exact hpower
  rw [hpower']
  field_simp [ne_of_gt hR, ne_of_gt he, hdne]
  ring

end

end CoarseDeGiorgi.SharpnessExamples
