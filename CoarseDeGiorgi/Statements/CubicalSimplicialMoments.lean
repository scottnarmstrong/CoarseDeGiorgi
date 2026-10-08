import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.UpperCellAverage
import CoarseDeGiorgi.Statements.LowerCellAverage
import CoarseDeGiorgi.Statements.CubeUpperCellAverage
import CoarseDeGiorgi.Statements.CubeLowerCellAverage
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.Cubical.MomentsMain
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Lemma `l.cubical.simplicial.moments` (finite `p` only), both choices of `𝐁`: upper `𝐚(U)` and lower `𝐚_*^{-1}(U)`. -/
theorem cubical_simplicial_moments (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
        (p : ℝ), 1 ≤ p → ∀ k : ℕ,
      ((ENNReal.ofReal (cubeUpperCellAverage a ha k p)).rpow (1 / p) ≤
          (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / p) ∧
        (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / p) ≤
          ENNReal.ofReal C *
            ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
              (ENNReal.ofReal (cubeUpperCellAverage a ha (k + l) p)).rpow (1 / p)) ∧
      ((ENNReal.ofReal (cubeLowerCellAverage a ha k p)).rpow (1 / p) ≤
          (ENNReal.ofReal (lowerCellAverage a ha k p)).rpow (1 / p) ∧
        (ENNReal.ofReal (lowerCellAverage a ha k p)).rpow (1 / p) ≤
          ENNReal.ofReal C *
            ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
              (ENNReal.ofReal (cubeLowerCellAverage a ha (k + l) p)).rpow (1 / p))
:=
  CoarseDeGiorgi.Cubical.cubical_simplicial_moments_main d

end CoarseDeGiorgi
