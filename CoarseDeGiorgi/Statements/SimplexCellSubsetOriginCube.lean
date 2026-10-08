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
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Moments.Cells

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem simplexCell_subset_originCube {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    simplexCell k η ⊆ originCube 1 :=
  CoarseDeGiorgi.Moments.simplexCell_subset_originCube k η

end CoarseDeGiorgi
