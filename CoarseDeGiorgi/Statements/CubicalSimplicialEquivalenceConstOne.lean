module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.CubeUpperMoment
public import CoarseDeGiorgi.Statements.CubeLowerMoment
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

public import CoarseDeGiorgi.Cubical.Comparison.Equivalence
public import CoarseDeGiorgi.Statements.CubicalSimplicialMoments

@[expose] public section

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
