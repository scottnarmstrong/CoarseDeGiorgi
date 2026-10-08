import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.GridOffset
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `e.cubical.family`: the cube `z + □_{-k}` of `𝒬_k`, `z = 3^{-k} • gridOffset k j ∈ 3^{-k}ℤ^d ∩ □₀`,
indexed as in `besovCubeNorm`. -/
def cubeCell {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Set (Vec d) :=
  {x | x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) ∈
    originCube ((3 : ℝ) ^ (-(k : ℤ)))}

end CoarseDeGiorgi
