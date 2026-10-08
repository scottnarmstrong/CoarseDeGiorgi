module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.CubeCell
public import CoarseDeGiorgi.Statements.CubeCellIsOpenBoundedConvexDomain
public import CoarseDeGiorgi.Statements.CubeCellNonempty
public import CoarseDeGiorgi.Statements.WeightedCoeffOnCubeCell
public import CoarseDeGiorgi.Statements.LowerResponseInv
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def lowerResponseInvOnCube {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (j : Fin d → Fin (3 ^ k)) : Mat d :=
  lowerResponseInv a (cubeCell k j)
    (cubeCell_isOpenBoundedConvexDomain k j)
    (cubeCell_nonempty k j)
    (weightedCoeffOn_cubeCell k a ha j)

end CoarseDeGiorgi
