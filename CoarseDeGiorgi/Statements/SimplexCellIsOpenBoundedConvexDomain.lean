import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.SimplexIndex
import CoarseDeGiorgi.Statements.SimplexCell
import CoarseDeGiorgi.Moments.Cells

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem simplexCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ)
    (η : SimplexIndex d k) : IsOpenBoundedConvexDomain (simplexCell k η) :=
  CoarseDeGiorgi.Moments.simplexCell_isOpenBoundedConvexDomain k η

end CoarseDeGiorgi
