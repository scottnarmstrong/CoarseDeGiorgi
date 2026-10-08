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

/-- Proposition `p.cubical.simplicial.equivalence`, last sentence: the inequalities with constant one hold for all `s, t > 0`,
`1 ≤ p, q` (finite). -/
theorem cubical_simplicial_equivalence_const_one (d : ℕ) (p q s t : ℝ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 0 < s) (ht : 0 < t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) :
    cubeUpperMoment a ha s p hs hp ≤ upperMoment a ha s p hs hp ∧
      lowerMoment a ha t q ht hq ≤ cubeLowerMoment a ha t q ht hq
:=
  by exact CoarseDeGiorgi.Cubical.cubical_simplicial_equivalence_const_one_of_moments d (CoarseDeGiorgi.cubical_simplicial_moments d) p q s t hp hq hs ht a ha

end CoarseDeGiorgi
