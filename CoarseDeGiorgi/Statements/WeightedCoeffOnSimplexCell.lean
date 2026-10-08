import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.SimplexIndex
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.SimplexCell
import CoarseDeGiorgi.Moments.Cells

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem weightedCoeffOn_simplexCell {d : ℕ} (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (η : SimplexIndex d k) : IsWeightedCoeffOn (simplexCell k η) a :=
  CoarseDeGiorgi.Moments.weightedCoeffOn_simplexCell k a ha η

end CoarseDeGiorgi
