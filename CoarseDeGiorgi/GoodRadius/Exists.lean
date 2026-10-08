module

public import CoarseDeGiorgi.GoodRadius.Main
public import CoarseDeGiorgi.Statements.FractionalLocalization

/-! Existence of good radii for the fractional trace and energy estimates. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.GoodRadius

theorem good_radius_exists_proved :
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
  by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C, hC, hgood⟩ := good_radius_of_localization
    (fun d hd => CoarseDeGiorgi.fractional_localization d hd) d hd p q s t hp hq hs ht hθ
  refine ⟨C, hC, ?_⟩
  intro a ha hrange v G hv hnn ρ₁ ρ₂ hρ₁ hgap hρ₂ hvr vi hsmooth hvinn hconv
  obtain ⟨τ, hτ, ns, hns, hcap, hrest⟩ :=
    hgood a ha hrange v G hv hnn ρ₁ ρ₂ hρ₁ hgap hρ₂ hvr vi hsmooth hvinn hconv
  exact ⟨τ, hτ, ns, hns, fun k N hN => (hcap k N hN).1, hrest⟩

end CoarseDeGiorgi.GoodRadius
