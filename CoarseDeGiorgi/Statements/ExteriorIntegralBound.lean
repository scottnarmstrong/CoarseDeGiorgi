module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.ClosedReferenceCube
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.SampledResponseSeries
public import CoarseDeGiorgi.Statements.SelectionInterval
public import CoarseDeGiorgi.Statements.SigmaLower
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
public import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
public import CoarseDeGiorgi.Statements.SurfaceMeasure

public import CoarseDeGiorgi.Statements.AffineExtension
public import CoarseDeGiorgi.Statements.HarmonicExtension
public import CoarseDeGiorgi.ExteriorIntegral.MainWide

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Lemma `l.exterior.integral`, estimates `e.summed.pairing` and `e.summed.pairing.lr`.  `(H, GH)` is the
piecewise harmonic extension `H_h g` of Section `s.whitney.extension` (`IsPiecewiseHarmonicExtension`);
`S(τ)` is `sampledResponseSeries`, `D_v(τ)` is `surfaceEnergyMaximal ρ₁ ρ₂`, `σ = sigmaUpper`,
`σ_* = sigmaLower`; `h^{-(σ+σ_*-t)}` is the `L^r` form.  The width is `0 < h ≤ δ/(200 d)` with `δ = ρ₂ - ρ₁`. -/
theorem exterior_integral_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
            ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
              let hτ0 : (1 / 2 : ℝ) ≤ τ := by
                have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
                linarith
              let hτ1 : τ < 1 := by
                have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
                linarith
              ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (200 * (d : ℝ)) →
                ∀ (g : Vec d → ℝ),
                  (∃ K : ℝ≥0, LipschitzOnWith K g (cubeSurface τ)) →
                    ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
                      MemH1a a (originCube 1) v G →
                      ∀ (H : Vec d → ℝ) (GH : Vec d → Vec d),
                        IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 g H GH →
                        Integrable (fun x => vecDot (GH x) (matVecMul (a x) (G x)))
                          (volume.restrict (originCube 1 \ closedReferenceCube (d := d) τ)) ∧
                        ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube (d := d) τ,
                          vecDot (GH x) (matVecMul (a x) (G x))| ≤
                          C * sampledResponseSeries a ha s p τ *
                            (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                            ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                              surfaceFracSeminorm τ (alphaParam t) (paramR q) g +
                              (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                                eLpNorm g 2 (surfaceMeasure τ)) ∧
                        ENNReal.ofReal |∫ x in originCube 1 \ closedReferenceCube (d := d) τ,
                          vecDot (GH x) (matVecMul (a x) (G x))| ≤
                          C * sampledResponseSeries a ha s p τ *
                            (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                            ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                              surfaceFracSeminorm τ (alphaParam t) (paramR q) g +
                              (ENNReal.ofReal h).rpow
                                (-(sigmaUpper d p s + sigmaLower d q t - t)) *
                                eLpNorm g (ENNReal.ofReal (paramR q)) (surfaceMeasure τ))
:=
  ExteriorIntegral.WideWidth.exterior_integral_bound_of_extension CoarseDeGiorgi.affine_extension CoarseDeGiorgi.harmonic_extension

end CoarseDeGiorgi
