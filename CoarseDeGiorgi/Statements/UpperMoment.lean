import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.UpperCellAverage

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def upperMoment {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s p : ℝ)
    (_hs : 0 < s) (_hp : 1 ≤ p) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / (2 * p))) ^ 2

end CoarseDeGiorgi
