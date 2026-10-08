import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.CubeLowerCellAverage
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `λ̃_{t,1,q}(□₀)` (`e.cubical.family` with Definition `d.cg.constants`, `𝗆 = 1`, `q < ∞`; compare `lowerMoment`). -/
noncomputable def cubeLowerMoment {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (t q : ℝ)
    (_ht : 0 < t) (_hq : 1 ≤ q) : ℝ≥0∞ :=
  (ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
    ∑' k : ℕ,
      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
        (ENNReal.ofReal (cubeLowerCellAverage a ha k q)).rpow (1 / (2 * q))).rpow (-2)

end CoarseDeGiorgi
