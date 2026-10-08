module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.IsSmoothCore
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.H1aWeightedNorm
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.PositiveCap
public import CoarseDeGiorgi.Statements.PositiveCapGradient
public import CoarseDeGiorgi.Statements.SampledResponseSeries
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.SmoothGrad
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import CoarseDeGiorgi.Statements.SurfaceFracNorm
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.SurfaceMeasure
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.UpperMoment

public import CoarseDeGiorgi.Statements.ExteriorIntegralBound
public import CoarseDeGiorgi.Statements.HarmonicExtension
public import CoarseDeGiorgi.Statements.ExistsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.GoodRadiusEnergy.MainWide

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.good.radius.energy`, estimate `e.good.radius.energy.estimate`: the energy of a truncation inside a good radius.  `v`, `(vᵢ)`,
`ρ₁ ρ₂` are as in Proposition `p.good.radius` (`good_radius_exists`); `τ ∈ J`, the subsequence `ns` and the constant `C₅` are a
good radius as given there: they satisfy the convergence `e.good.radius.convergence` of the truncations in `W^{1-t,r}(∂(τ□₀))` for
every `k` and `0 < N ≤ ∞`, the bounds `e.good.radius.matrices` and `e.good.radius.boundary.energy`, and `D_w ≤ D_v` everywhere for every truncation.  The
`L²` convergence on `∂(τ□₀)` is not a hypothesis (the proof derives it from Lemma `l.critical.trace.embedding`).  The width is
`0 < h ≤ δ/(200 d)` with `δ = ρ₂ - ρ₁`. -/
theorem good_radius_energy_bound :
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
                ∀ τ ∈ selectionInterval ρ₁ ρ₂, ∀ ns : ℕ → ℕ, StrictMono ns →
                  ∀ C₅ : ℝ≥0∞, C₅ < ⊤ →
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N →
                    Filter.Tendsto
                      (fun i => surfaceFracNorm τ (alphaParam t) (paramR q)
                        (fun x => positiveCap (vᵢ (ns i)) k N x - positiveCap v k N x))
                      Filter.atTop (nhds 0)) →
                  sampledResponseSeries a ha s p τ ≤
                    C₅ * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / (2 * p))) *
                      (upperMoment a ha s p hs (le_of_lt hp)).rpow (1 / 2) →
                  surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ ≤
                    C₅ * (ENNReal.ofReal (ρ₂ - ρ₁))⁻¹ *
                      weightedEnergy a (originCube ρ₂) G →
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N → ∀ τ' : ℝ,
                    surfaceEnergyMaximal ρ₁ ρ₂ a ha (positiveCapGradient v G k N) τ' ≤
                      surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ') →
                  ∀ k : ℝ,
                    IsWeightedSubsolution a (originCube 1) (positiveCap v k ⊤)
                      (positiveCapGradient v G k ⊤) →
                    ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (200 * (d : ℝ)) →
                      weightedEnergy a (originCube τ) (positiveCapGradient v G k ⊤) ≤
                        C * sampledResponseSeries a ha s p τ *
                          (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                          ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                            surfaceFracSeminorm τ (alphaParam t) (paramR q)
                              (positiveCap v k ⊤) +
                            (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                              eLpNorm (positiveCap v k ⊤) 2 (surfaceMeasure τ))
:=
  GoodRadiusEnergy.WideWidth.good_radius_energy_bound_of_extension CoarseDeGiorgi.exterior_integral_bound CoarseDeGiorgi.harmonic_extension CoarseDeGiorgi.exists_piecewiseHarmonicExtension

end CoarseDeGiorgi
