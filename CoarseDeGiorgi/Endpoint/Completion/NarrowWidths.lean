module

public import CoarseDeGiorgi.PowerCacc.Hypotheses
public import CoarseDeGiorgi.Statements.ExteriorIntegralBound
public import CoarseDeGiorgi.Statements.HarmonicExtension
public import CoarseDeGiorgi.Statements.ExistsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.Statements.GoodRadiusEnergyBound

/-! Compatibility with the existing narrow-width implementation APIs, using the paper’s extension and energy estimates. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi.Endpoint

/-- `l.exterior.integral` for triadic widths at most δ/(20000 d). -/
theorem exterior_integral_narrow : PowerCacc.ExteriorIntegralHyp := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C, hC, hbound⟩ := exterior_integral_bound d hd p q s t hp hq hs ht hθ
  refine ⟨C, hC, ?_⟩
  intro a ha hrange ρ₁ ρ₂ hρ₁ hgap hρ₂ τ hJ
  dsimp only
  intro h htri hw
  apply hbound a ha hrange ρ₁ ρ₂ hρ₁ hgap hρ₂ τ hJ h htri
  exact hw.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr hgap.le) (by positivity)
    (by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith))

open scoped Classical in
/-- `p.whitney.extension` for triadic widths at most (ρ₂ − τ)/(10000 d). -/
theorem harmonic_extension_narrow : PowerCacc.WhitneyHarmonicExtensionHyp := by
  intro d hd α ξ hα0 hα1 hξ1 hξ2
  obtain ⟨C, hC, hbound⟩ := harmonic_extension d hd α ξ hα0 hα1 hξ1 hξ2
  refine ⟨C, hC, ?_⟩
  intro a ha ρ₁ ρ₂ hρ₁ hgap hρ₂ τ hJ
  dsimp only
  intro h htri hw
  apply hbound a ha ρ₁ ρ₂ hρ₁ hgap hρ₂ τ hJ h htri
  exact hw.trans (div_le_div_of_nonneg_left (by linarith [hJ.2]) (by positivity)
    (by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith))

/-- Existence of the piecewise harmonic extension at the narrower triadic widths. -/
theorem exists_piecewiseHarmonicExtension_narrow : PowerCacc.PiecewiseHarmonicExtensionExistsHyp := by
  intro d hd a ha ρ₁ ρ₂ hρ₁ hgap hρ₂ τ hJ
  dsimp only
  intro h htri hw
  apply exists_piecewiseHarmonicExtension d hd a ha ρ₁ ρ₂ hρ₁ hgap hρ₂ τ hJ h htri
  exact hw.trans (div_le_div_of_nonneg_left (by linarith [hJ.2]) (by positivity)
    (by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith))

/-- `p.good.radius.energy` for triadic widths at most δ/(20000 d), using fractional trace convergence. -/
theorem good_radius_energy_narrow :
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
                    ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (20000 * (d : ℝ)) →
                      weightedEnergy a (originCube τ) (positiveCapGradient v G k ⊤) ≤
                        C * sampledResponseSeries a ha s p τ *
                          (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                          ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                            surfaceFracSeminorm τ (alphaParam t) (paramR q)
                              (positiveCap v k ⊤) +
                            (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                              eLpNorm (positiveCap v k ⊤) 2 (surfaceMeasure τ)) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C, hC, hbound⟩ := good_radius_energy_bound d hd p q s t hp hq hs ht hθ
  refine ⟨C, hC, ?_⟩
  intro a ha hrange v G hv hv0 ρ₁ ρ₂ hρ₁ hgap hρ₂ hvr vi hvi hvi0 hlim τ hJ ns hns
    C₅ hC₅ hconv hS hD hmax k hsub h htri hw
  apply hbound a ha hrange v G hv hv0 ρ₁ ρ₂ hρ₁ hgap hρ₂ hvr vi hvi hvi0 hlim τ hJ ns hns
    C₅ hC₅ hconv hS hD hmax k hsub h htri
  exact hw.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr hgap.le) (by positivity)
    (by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith))

end CoarseDeGiorgi.Endpoint
