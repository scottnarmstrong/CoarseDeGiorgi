import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.CubeUpperCellAverage
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `Λ̃_{s,1,p}(□₀)` (`e.cubical.family` with Definition `d.cg.constants`, `𝗆 = 1`, `p < ∞`; compare `upperMoment`,
which is the square `Λ_{s,1,p}`). -/
noncomputable def cubeUpperMoment {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s p : ℝ)
    (_hs : 0 < s) (_hp : 1 ≤ p) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (cubeUpperCellAverage a ha k p)).rpow (1 / (2 * p))) ^ 2

end CoarseDeGiorgi
