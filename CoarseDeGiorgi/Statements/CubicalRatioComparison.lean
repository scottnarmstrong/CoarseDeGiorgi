module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.CubeContrast
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

public import CoarseDeGiorgi.Cubical.Comparison.Consequences

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `e.cubical.simplicial.ratio`: `Θ̃ ≤ Θ ≤ C Θ̃` in the range `e.cubical.simplicial.range`. -/
theorem cubical_ratio_comparison (d : ℕ) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        cubeContrast a ha s t p q hs ht hp.le hq.le ≤ contrast a ha s t p q hs ht hp.le hq.le ∧
          contrast a ha s t p q hs ht hp.le hq.le ≤
            ENNReal.ofReal C * cubeContrast a ha s t p q hs ht hp.le hq.le
:=
  by exact CoarseDeGiorgi.Cubical.cubical_ratio_comparison_of_equivalence d p q s t hp hq hs ht _hsp _htq

end CoarseDeGiorgi
