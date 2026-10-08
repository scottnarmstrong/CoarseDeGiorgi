module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.GridOffset
public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `e.cubical.family`: the cube `z + □_{-k}` of `𝒬_k`, `z = 3^{-k} • gridOffset k j ∈ 3^{-k}ℤ^d ∩ □₀`,
indexed as in `besovCubeNorm`. -/
def cubeCell {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Set (Vec d) :=
  {x | x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) ∈
    originCube ((3 : ℝ) ^ (-(k : ℤ)))}

end CoarseDeGiorgi
