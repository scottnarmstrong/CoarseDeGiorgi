import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.AuxCube
import CoarseDeGiorgi.Statements.FracSeminorm
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.WeightedEnergy

import CoarseDeGiorgi.LowerFractional.CubeFinal
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.lower.fractional`, the bound `e.lower.fractional`: for every triadic cube
`Q = auxCube m z ⊆ □₀` (the cube `3^{-m} z + □_{1-m}`; the inclusion
forces `m ≥ 1`, i.e. the paper's `n = m - 1 ∈ ℕ₀`) (cubes touching `∂□₀`, and `□₀` itself, included) and `w ∈ H¹_a(Q)`,
`[w]_{W^{1-t,r}(Q)} ≤ C λ_{t,1,q}(□₀)^{-1/2} ℰ_Q(w)^{1/2}`, with `C = C(d, q, t)`. -/
theorem lower_fractional_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ q t : ℝ, (hq : 1 < q) → (ht : 0 < t) →
      ∃ C : ℝ, 0 < C ∧
        ∀ p s : ℝ, (hp : 1 < p) → (hs : 0 < s) →
          ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
            spatialMomentRange a ha p q s t →
            ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (G : Vec d → Vec d),
              auxCube m z ⊆ originCube 1 → MemH1a a (auxCube m z) w G →
              fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
                ENNReal.ofReal C *
                  ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2) *
                  ENNReal.rpow (weightedEnergy a (auxCube m z) G) (1 / 2)
:=
  LowerFractional.lower_fractional_bound_of_reconstruction LowerFractional.cube_reconstruction

end CoarseDeGiorgi
