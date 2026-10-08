import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.CubeContrast
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.Cubical.Comparison.Consequences
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
