import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.CubeCell
import CoarseDeGiorgi.Statements.CubeCellIsOpenBoundedConvexDomain
import CoarseDeGiorgi.Statements.CubeCellNonempty
import CoarseDeGiorgi.Statements.WeightedCoeffOnCubeCell
import CoarseDeGiorgi.Statements.UpperResponse
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def upperResponseOnCube {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (j : Fin d → Fin (3 ^ k)) : Mat d :=
  upperResponse a (cubeCell k j)
    (cubeCell_isOpenBoundedConvexDomain k j)
    (cubeCell_nonempty k j)
    (weightedCoeffOn_cubeCell k a ha j)

end CoarseDeGiorgi
