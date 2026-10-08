import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.UpperResponseOnCube
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Mean over `𝒬_k` of `|𝐚(Q)|^p`; the `3^{kd}` cubes are indexed by `Fin d → Fin (3^k)`. -/
noncomputable def cubeUpperCellAverage {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (p : ℝ) : ℝ :=
  (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖upperResponseOnCube k a ha j‖ p) /
    ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)

end CoarseDeGiorgi
