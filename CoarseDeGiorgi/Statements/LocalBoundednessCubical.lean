module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.CubeContrast
public import CoarseDeGiorgi.Statements.CubeUpperMoment
public import CoarseDeGiorgi.Statements.CubeLowerMoment
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.LocallyBoundedAbove
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

public import CoarseDeGiorgi.Cubical.Comparison.Theorems

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Theorem A and Corollary B with `Θ̃` in place of `Θ` (the sentence after `e.cubical.simplicial.ratio`),
in the range `e.cubical.simplicial.range`,
with the moment conditions computed on cubes (`Λ̃ < ∞`, `λ̃ > 0`). Same shape as `local_boundedness`. -/
theorem local_boundedness_cubical (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ γ : ℝ, 0 < γ ∧
      ((∃ C_A : ℝ, 0 ≤ C_A ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          LocallyBoundedAbove (originCube 1) u ∧
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_A *
            (ENNReal.ofReal (R - ρ)).rpow (-γ) *
            (cubeContrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (4 * paramTheta d p q s t)) *
            eLpNorm (positivePart u) 2 (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) 2
              (volume.restrict (originCube R)) < ⊤)) ∧
      (∀ η : ℝ, 0 < η → η < 2 →
        ∃ C_η : ℝ, 0 ≤ C_η ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_η *
            (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)) *
            (cubeContrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (2 * η * paramTheta d p q s t)) *
            eLpNorm (positivePart u) (ENNReal.ofReal η) (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) (ENNReal.ofReal η)
              (volume.restrict (originCube R)) < ⊤)))
:=
  by exact CoarseDeGiorgi.Cubical.local_boundedness_cubical_of_equivalence d _hd p q s t hp hq hs ht _hθ _hsp _htq

end CoarseDeGiorgi
