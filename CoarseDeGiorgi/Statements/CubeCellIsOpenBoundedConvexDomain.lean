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

public import CoarseDeGiorgi.Moments.CubeCells

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem cubeCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    IsOpenBoundedConvexDomain (cubeCell k j)
:=
  CoarseDeGiorgi.Moments.cubeCell_isOpenBoundedConvexDomain k j

end CoarseDeGiorgi
