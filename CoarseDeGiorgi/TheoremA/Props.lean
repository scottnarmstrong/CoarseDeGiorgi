module

public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.LocallyBoundedAbove
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.GammaCacc
public import CoarseDeGiorgi.Statements.GammaSup
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.SigmaLower
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.TwoLevelQuantity
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.WeightedEnergy

/-! The statements of Propositions `p.cg.caccioppoli` and `p.energy.to.sup` as propositions, copied
verbatim from `caccioppoli_inequality` and `energy_to_supremum` (which are not imported). -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.TheoremA

/-- Statement of Proposition `p.cg.caccioppoli` (`caccioppoli_inequality`). -/
abbrev Prop81 : Prop :=
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
          spatialMomentRange a ha p q s t →
          ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ v x) →
            (hv : IsWeightedSubsolution a (originCube 1) v G) →
            ∀ ρ₁ ρ₂ : ℝ, (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              weightedEnergy a (originCube ρ₁) G ≤
                C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaCacc d p q s t) *
                  upperMoment a ha s p hs (le_of_lt hp) *
                  ENNReal.rpow (contrast a ha s t p q hs ht
                    (le_of_lt hp) (le_of_lt hq))
                    (sigmaUpper d p s / paramTheta d p q s t) *
                  ENNReal.rpow
                    (eLpNorm v 2 (volume.restrict (originCube ρ₂))) 2

/-- Statement of Proposition `p.energy.to.sup` (`energy_to_supremum`). -/
abbrev Prop83 : Prop :=
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
          spatialMomentRange a ha p q s t →
          (∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (hu : IsWeightedSubsolution a (originCube 1) u G) →
            ∀ ρ₁ ρ₂ : ℝ, (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              twoLevelQuantity a ha q t ht (le_of_lt hq) u G 0 ρ₂ < ⊤ →
              eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ₁)) ≤
                C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaSup d p q s t) *
                  ENNReal.rpow (contrast a ha s t p q hs ht
                    (le_of_lt hp) (le_of_lt hq))
                    (((d : ℝ) - 3 + 2 * sigmaLower d q t) /
                      (4 * paramTheta d p q s t)) *
                  twoLevelQuantity a ha q t ht (le_of_lt hq) u G 0 ρ₂) ∧
          (∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSubsolution a (originCube 1) u G →
            LocallyBoundedAbove (originCube 1) u)

end CoarseDeGiorgi.TheoremA
