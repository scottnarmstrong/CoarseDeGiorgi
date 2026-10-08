module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.UpperResponseOnCube
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Mean over `𝒬_k` of `|𝐚(Q)|^p`; the `3^{kd}` cubes are indexed by `Fin d → Fin (3^k)`. -/
noncomputable def cubeUpperCellAverage {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (p : ℝ) : ℝ :=
  (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖upperResponseOnCube k a ha j‖ p) /
    ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)

end CoarseDeGiorgi
