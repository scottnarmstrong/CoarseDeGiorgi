import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.CubeCell

import CoarseDeGiorgi.Moments.CubeCells
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem cubeCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    IsOpenBoundedConvexDomain (cubeCell k j)
:=
  CoarseDeGiorgi.Moments.cubeCell_isOpenBoundedConvexDomain k j

end CoarseDeGiorgi
