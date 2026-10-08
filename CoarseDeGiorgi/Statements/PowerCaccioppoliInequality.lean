import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PowerFactor
import CoarseDeGiorgi.Statements.SigmaLower
import CoarseDeGiorgi.Statements.SigmaUpper
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.WeightedEnergy

import CoarseDeGiorgi.Endpoint.Completion.NarrowWidths
import CoarseDeGiorgi.PowerCacc.Final
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.power.caccioppoli`, estimate `e.power.caccioppoli`.  The power of
`(ρ₂-ρ₁)^{-1}` is `2γ₁(1-t)/θ` (`γ₁ = gammaLoc`, `1-t = alphaParam t`); the weighted factor
`1 + c_m²Θ` (`c_m = powerFactor m`) keeps its `1 +`, with exponent `(σ+σ_*-t)/θ`. -/
theorem power_caccioppoli_inequality :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε →
              ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
                ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
                  weightedEnergy a (originCube ρ₁)
                    (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow
                        (-2 * gammaLoc p q t * alphaParam t /
                          paramTheta d p q s t) *
                      upperMoment a ha s p hs (le_of_lt hp) *
                      ENNReal.ofReal (powerFactor m ^ 2) *
                      (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                        contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                          ((sigmaUpper d p s + sigmaLower d q t - t) /
                            paramTheta d p q s t) *
                      (eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube ρ₂))).rpow 2
:=
  PowerCacc.power_caccioppoli_inequality_of_extension Endpoint.exterior_integral_narrow Endpoint.harmonic_extension_narrow Endpoint.exists_piecewiseHarmonicExtension_narrow

end CoarseDeGiorgi
