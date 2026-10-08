import CoarseDeGiorgi.Statements.IsFractionalCover
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Statements.FracNorm
import CoarseDeGiorgi.Statements.H1aWeightedNorm
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.WeightedEnergy

/-!
# The localization hypothesis of Proposition `p.good.radius`

`FractionalLocalizationHyp d` is, verbatim, the conclusion of Proposition
`p.fractional.localization` (`fractional_localization`) in dimension `d`. The good-radius selection
is proved from it as an explicit hypothesis, so that this development does not import
`fractional_localization`.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.GoodRadius

def FractionalLocalizationHyp (d : ℕ) : Prop :=
      ∃ (S : ℝ → ℝ → Finset (ℤ × (Fin d → ℤ)))
      (φ : ℝ → ℝ → ℤ × (Fin d → ℤ) → Vec d → ℝ)
      (S' : ℝ → ℝ → Finset (ℤ × (Fin d → ℤ)))
      (φ' : ℝ → ℝ → ℤ × (Fin d → ℤ) → Vec d → ℝ),
    (∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      IsFractionalCover ρ₂ (S ρ₁ ρ₂) (φ ρ₁ ρ₂) ∧
      IsFractionalCover ρ₂ (S' ρ₁ ρ₂) (φ' ρ₁ ρ₂)) ∧
    ∀ p q s t : ℝ, (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
            (∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
              MemH1a a (originCube 1) v G →
              (∀ τ ∈ selectionInterval ρ₁ ρ₂,
                ∃ U : Set (Vec d), IsOpen U ∧ cubeSurface τ ⊆ U ∧
                  ∀ᵐ x ∂(volume.restrict U),
                    ∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * v x = v x) ∧
              fracNorm Set.univ (alphaParam t) (paramR q)
                  (fun x => ∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * v x) ≤
                C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t) *
                  ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
                      (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
                    eLpNorm v (ENNReal.ofReal (paramR q))
                      (volume.restrict (originCube ρ₂))) ∧
              ∀ (vⱼ : ℕ → Vec d → ℝ) (Gⱼ : ℕ → Vec d → Vec d),
                (∀ j, MemH1a a (originCube 1) (vⱼ j) (Gⱼ j)) →
                Filter.Tendsto
                  (fun j => h1aWeightedNorm a (originCube 1)
                    (fun x => vⱼ j x - v x) (fun x => Gⱼ j x - G x))
                  Filter.atTop (nhds 0) →
                Filter.Tendsto
                  (fun j => fracNorm Set.univ (alphaParam t) (paramR q)
                    (fun x => (∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * vⱼ j x) -
                      ∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * v x))
                  Filter.atTop (nhds 0)) ∧
            (∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
              MemH1a a (originCube 1) v G →
              (∃ U : Set (Vec d), IsOpen U ∧ closure (originCube ρ₁) ⊆ U ∧
                ∀ᵐ x ∂(volume.restrict U),
                  ∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * v x = v x) ∧
              fracNorm Set.univ (alphaParam t) (paramR q)
                  (fun x => ∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * v x) ≤
                C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t) *
                  ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
                      (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
                    eLpNorm v (ENNReal.ofReal (paramR q))
                      (volume.restrict (originCube ρ₂))) ∧
              ∀ (vⱼ : ℕ → Vec d → ℝ) (Gⱼ : ℕ → Vec d → Vec d),
                (∀ j, MemH1a a (originCube 1) (vⱼ j) (Gⱼ j)) →
                Filter.Tendsto
                  (fun j => h1aWeightedNorm a (originCube 1)
                    (fun x => vⱼ j x - v x) (fun x => Gⱼ j x - G x))
                  Filter.atTop (nhds 0) →
                Filter.Tendsto
                  (fun j => fracNorm Set.univ (alphaParam t) (paramR q)
                    (fun x => (∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * vⱼ j x) -
                      ∑ i ∈ S' ρ₁ ρ₂, φ' ρ₁ ρ₂ i x * v x))
                  Filter.atTop (nhds 0))

end CoarseDeGiorgi.GoodRadius
