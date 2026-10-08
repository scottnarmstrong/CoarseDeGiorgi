import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.CubeUpperMoment
import CoarseDeGiorgi.Statements.CubeLowerMoment
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.Cubical.Comparison.Equivalence
import CoarseDeGiorgi.Statements.CubicalSimplicialMoments
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.cubical.simplicial.equivalence` for `𝗆 = 1` and finite `p, q`: the comparison
`e.Lambda.cube.simplex.equivalence`, `e.lambda.cube.simplex.equivalence` in the range
`e.cubical.simplicial.range`. `upperMoment` and `cubeUpperMoment` are the squares `Λ`, `Λ̃`, as the
manuscript defines them. -/
theorem cubical_simplicial_equivalence (d : ℕ) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        (cubeUpperMoment a ha s p hs hp.le ≤ upperMoment a ha s p hs hp.le ∧
          upperMoment a ha s p hs hp.le ≤
            ENNReal.ofReal C * cubeUpperMoment a ha s p hs hp.le) ∧
        (ENNReal.ofReal C⁻¹ * cubeLowerMoment a ha t q ht hq.le ≤ lowerMoment a ha t q ht hq.le ∧
          lowerMoment a ha t q ht hq.le ≤ cubeLowerMoment a ha t q ht hq.le)
:=
  by exact CoarseDeGiorgi.Cubical.cubical_simplicial_equivalence_of_moments d (CoarseDeGiorgi.cubical_simplicial_moments d) p q s t hp hq hs ht _hsp _htq

end CoarseDeGiorgi
