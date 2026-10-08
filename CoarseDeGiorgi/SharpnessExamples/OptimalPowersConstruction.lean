import CoarseDeGiorgi.SharpnessExamples.PolynomialEquationWeak
import CoarseDeGiorgi.SharpnessExamples.OptimalPowersField
import CoarseDeGiorgi.Weighted.ResponseBounds
import CoarseDeGiorgi.Weighted.TestingTruncation
import CoarseDeGiorgi.Whitney.ExteriorCells

open Homogenization MeasureTheory

namespace CoarseDeGiorgi.SharpnessExamples

/-- The explicit cylinder solution has a positive-part weighted subsolution. -/
theorem optimalPowers_solution_posPartSubsolution {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1 / 8) :
    IsWeightedSolution (polynomialCoefficientFamily d q t epsilon)
        (originCube (d := d) 1) (polynomialSolution d q t epsilon)
        (polynomialGradient d q t epsilon) ∧
      ∃ G' : Vec d → Vec d,
        IsWeightedSubsolution (polynomialCoefficientFamily d q t epsilon)
          (originCube (d := d) 1)
          (positivePart (polynomialSolution d q t epsilon)) G' := by
  have hsol := polynomialSolution_isWeightedSolution (d := d) (q := q) (t := t)
    (epsilon := epsilon) hd he he8
  have hV := Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1)
  have hne := Whitney.source_cube_nonempty (d := d) (by norm_num : (0 : ℝ) < 1)
  have ha := optimalPowers_family_weightedCoeffOn d hd q t epsilon
  have hsub := Weighted.response_solution_subsolution hsol
  have hpos := Weighted.IsWeightedSubsolution.posPart hV hne ha hsub
  refine ⟨hsol, ?_⟩
  change ∃ G' : Vec d → Vec d,
    IsWeightedSubsolution (polynomialCoefficientFamily d q t epsilon)
      (originCube (d := d) 1)
      (fun x => max (polynomialSolution d q t epsilon x) 0) G'
  exact ⟨_, hpos⟩

end CoarseDeGiorgi.SharpnessExamples
