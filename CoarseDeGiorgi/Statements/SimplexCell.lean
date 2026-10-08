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
public import CoarseDeGiorgi.Statements.Simplex

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

def simplexCell {d : ℕ} (k : ℕ) (η : SimplexIndex d k) : Set (Vec d) :=
  simplex (-(k : ℤ)) η.1.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η.1.1 i : ℝ))

end CoarseDeGiorgi
