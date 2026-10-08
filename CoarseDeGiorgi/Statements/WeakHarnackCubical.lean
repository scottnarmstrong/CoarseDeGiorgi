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
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.NormalizedLpMoment
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

public import CoarseDeGiorgi.Cubical.Comparison.Theorems
public import CoarseDeGiorgi.Statements.WeakHarnackRange
public import CoarseDeGiorgi.Statements.CubicalSimplicialEquivalence
public import CoarseDeGiorgi.Statements.CubicalRatioComparison

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The weak Harnack inequality `e.weak.harnack` for every `0 < η ≤ r*/2` (as `weak_harnack_range`) with `Θ̃`
in place of `Θ` (the sentence after `e.cubical.simplicial.ratio`), in the range `e.cubical.simplicial.range`, with the moment conditions computed on cubes. -/
theorem weak_harnack_cubical (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∀ (η : ℝ) (hη : 0 < η), η ≤ rStarParam (d := d) q t / 2 →
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment η hη (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u
:=
  by
    exact CoarseDeGiorgi.Cubical.weak_harnack_cubical_of_equivalence
      d _hd p q s t hp hq hs ht _hθ _hsp _htq
      (CoarseDeGiorgi.weak_harnack_range d _hd p q s t hp hq hs ht _hθ)

end CoarseDeGiorgi
