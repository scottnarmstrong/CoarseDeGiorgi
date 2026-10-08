import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.LowerResponseInvOnCube
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Mean over `𝒬_k` of `|𝐚_*^{-1}(Q)|^q`. -/
noncomputable def cubeLowerCellAverage {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (q : ℝ) : ℝ :=
  (∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖lowerResponseInvOnCube k a ha j‖ q) /
    ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ)

end CoarseDeGiorgi
