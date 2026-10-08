import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.CubeContrast
import CoarseDeGiorgi.Statements.CubeUpperMoment
import CoarseDeGiorgi.Statements.CubeLowerMoment
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.Cubical.Comparison.Theorems
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The Harnack inequality `e.harnack` with `Θ̃` in place of `Θ` (the sentence after `e.cubical.simplicial.ratio`),
in the range `e.cubical.simplicial.range`,
with the moment conditions computed on cubes. Same shape as `harnack`. -/
theorem harnack_cubical (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t)
    (_hsp : s < (1 / 2) * (1 - 1 / p)) (_htq : t < (1 / 2) * (1 - 1 / q)) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          cubeUpperMoment a ha s p hs hp.le < ⊤ →
          0 < cubeLowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSolution a (originCube 1) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (cubeContrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u
:=
  by exact CoarseDeGiorgi.Cubical.harnack_cubical_of_equivalence d _hd p q s t hp hq hs ht _hθ _hsp _htq

end CoarseDeGiorgi
