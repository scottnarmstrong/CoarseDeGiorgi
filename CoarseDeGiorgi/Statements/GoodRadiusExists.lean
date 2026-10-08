import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsSmoothCore
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Statements.H1aWeightedNorm
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PositiveCap
import CoarseDeGiorgi.Statements.PositiveCapGradient
import CoarseDeGiorgi.Statements.SampledResponseSeries
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.SmoothGrad
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
import CoarseDeGiorgi.Statements.SurfaceFracNorm
import CoarseDeGiorgi.Statements.SurfaceMeasure
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.WeightedEnergy

import CoarseDeGiorgi.GoodRadius.Exists
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.good.radius`, existence of a good radius.  The truncations converge in
`W^{1-t,r}(∂(τ□₀))` only (`e.good.radius.convergence`); the `L²` convergence is not part of the statement. -/
theorem good_radius_exists :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
            MemH1a a (originCube 1) v G →
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ v x) →
            ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              eLpNorm v (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube ρ₂)) < ⊤ →
              ∀ vᵢ : ℕ → Vec d → ℝ,
                (∀ i, IsSmoothCore a (originCube 1) (vᵢ i)) →
                (∀ i, ∀ x ∈ originCube (d := d) 1, 0 ≤ vᵢ i x) →
                Filter.Tendsto
                  (fun i => h1aWeightedNorm a (originCube 1)
                    (fun x => vᵢ i x - v x)
                    (fun x => smoothGrad (vᵢ i) x - G x))
                  Filter.atTop (nhds 0) →
                ∃ τ ∈ selectionInterval ρ₁ ρ₂, ∃ ns : ℕ → ℕ, StrictMono ns ∧
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N →
                    Filter.Tendsto
                      (fun i => surfaceFracNorm τ (alphaParam t) (paramR q)
                        (fun x => positiveCap (vᵢ (ns i)) k N x - positiveCap v k N x))
                      Filter.atTop (nhds 0)) ∧
                  sampledResponseSeries a ha s p τ ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / (2 * p))) *
                      (upperMoment a ha s p hs (le_of_lt hp)).rpow (1 / 2) ∧
                  surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁))⁻¹ *
                      weightedEnergy a (originCube ρ₂) G ∧
                  surfaceFracNorm τ (alphaParam t) (paramR q) v ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t - 1 / paramR q) *
                      ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
                        (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
                        eLpNorm v (ENNReal.ofReal (paramR q))
                          (volume.restrict (originCube ρ₂))) ∧
                  eLpNorm v (ENNReal.ofReal (paramR q)) (surfaceMeasure τ) ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / paramR q)) *
                      eLpNorm v (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube ρ₂)) ∧
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N → ∀ τ' : ℝ,
                    surfaceEnergyMaximal ρ₁ ρ₂ a ha (positiveCapGradient v G k N) τ' ≤
                      surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ') ∧
                  (eLpNorm v 2 (volume.restrict (originCube ρ₂)) < ⊤ →
                    eLpNorm v 2 (surfaceMeasure τ) ≤
                      C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / 2)) *
                        eLpNorm v 2 (volume.restrict (originCube ρ₂)))
:=
  CoarseDeGiorgi.GoodRadius.good_radius_exists_proved

end CoarseDeGiorgi
