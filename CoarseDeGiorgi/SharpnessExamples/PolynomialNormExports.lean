import CoarseDeGiorgi.SharpnessExamples.PolynomialNorms
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.IsWeightedSubsolution

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

theorem polynomialPositivePart_height_of_solution {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t : ℝ}
    (hsolution : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      IsWeightedSolution (polynomialCoefficientFamily d q t epsilon)
        (originCube 1) (polynomialSolution d q t epsilon)
        (polynomialGradient d q t epsilon) ∧
      ∃ G' : Vec d → Vec d,
        IsWeightedSubsolution (polynomialCoefficientFamily d q t epsilon)
          (originCube 1) (positivePart (polynomialSolution d q t epsilon)) G')
    {epsilon rho : ℝ} (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8)
    (hrho : 1 / 2 ≤ rho) (hrho1 : rho < 1) :
    eLpNorm (positivePart (polynomialSolution d q t epsilon)) ⊤
      (volume.restrict (originCube rho)) = ENNReal.ofReal (1 + rho ^ 2 / 4) := by
  have hu : AEStronglyMeasurable (polynomialSolution d q t epsilon)
      (volume.restrict (originCube 1)) :=
    (hsolution epsilon hepsilon hepsilon8).1.1.1
  have hpositive : AEStronglyMeasurable
      (positivePart (polynomialSolution d q t epsilon))
      (volume.restrict (originCube 1)) := by
    change AEStronglyMeasurable (fun x => max (polynomialSolution d q t epsilon x) 0) _
    exact (by fun_prop : Continuous (fun y : ℝ => max y 0)).comp_aestronglyMeasurable hu
  exact polynomialPositivePart_height hd hepsilon hepsilon8 hpositive hrho hrho1

theorem polynomialPositivePart_Lp_asymptotic_of_solution {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {q t eta : ℝ} (heta : 0 < eta)
    (hsolution : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      IsWeightedSolution (polynomialCoefficientFamily d q t epsilon)
        (originCube 1) (polynomialSolution d q t epsilon)
        (polynomialGradient d q t epsilon) ∧
      ∃ G' : Vec d → Vec d,
        IsWeightedSubsolution (polynomialCoefficientFamily d q t epsilon)
          (originCube 1) (positivePart (polynomialSolution d q t epsilon)) G') :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ∀ R : ℝ, 1 / 2 < R → R ≤ 1 →
        ENNReal.ofReal (C⁻¹ * epsilon ^ (((d : ℝ) - 1) / eta)) ≤
          eLpNorm (positivePart (polynomialSolution d q t epsilon)) (ENNReal.ofReal eta)
            (volume.restrict (originCube R)) ∧
        eLpNorm (positivePart (polynomialSolution d q t epsilon)) (ENNReal.ofReal eta)
            (volume.restrict (originCube R)) ≤
          ENNReal.ofReal (C * epsilon ^ (((d : ℝ) - 1) / eta)) := by
  apply polynomialPositivePart_Lp_asymptotic hd heta
  intro epsilon hepsilon hepsilon8
  have hu : AEStronglyMeasurable (polynomialSolution d q t epsilon)
      (volume.restrict (originCube 1)) :=
    (hsolution epsilon hepsilon hepsilon8).1.1.1
  change AEStronglyMeasurable (fun x => max (polynomialSolution d q t epsilon x) 0) _
  exact (by fun_prop : Continuous (fun y : ℝ => max y 0)).comp_aestronglyMeasurable hu

end CoarseDeGiorgi.SharpnessExamples
