import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
import CoarseDeGiorgi.Statements.IsTriadicWidth
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube

import CoarseDeGiorgi.Whitney.Harmonic.ExistsWide
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- Auxiliary (not a numbered statement): the piecewise harmonic extension `H_h f`
exists, i.e. the relation `IsPiecewiseHarmonicExtension` is satisfiable (the harmonic
representatives of Proposition `p.harmonic.replacement` on the simplices of `𝒲_h`).  The width is
`h ≤ (ρ₂-τ)/(100 d)` (`e.extension.width`). -/
theorem exists_piecewiseHarmonicExtension :
    ∀ d : ℕ, 3 ≤ d → ∀ a : CoeffField d,
      IsWeightedCoeffOn (originCube 1) a →
      ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
          let hτ0 : (1 / 2 : ℝ) ≤ τ := by
            have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
            linarith
          let hτ1 : τ < 1 := by
            have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
            linarith
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (100 * (d : ℝ)) →
            ∀ f : Vec d → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K f (cubeSurface τ)) →
              ∃ (H : Vec d → ℝ) (GH : Vec d → Vec d),
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH
:=
  Whitney.Harmonic.Wide.piecewiseHarmonicExtension_exists_proved

end CoarseDeGiorgi
