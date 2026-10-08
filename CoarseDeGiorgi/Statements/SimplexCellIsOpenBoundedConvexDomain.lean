module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Moments.Cells

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem simplexCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ)
    (η : SimplexIndex d k) : IsOpenBoundedConvexDomain (simplexCell k η) :=
  CoarseDeGiorgi.Moments.simplexCell_isOpenBoundedConvexDomain k η

end CoarseDeGiorgi
