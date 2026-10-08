module

public import CoarseDeGiorgi.TheoremA.Estimate
public import CoarseDeGiorgi.TheoremA.Eta
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.LocallyBoundedAbove

/-! Theorem A and Corollary B (the statement of `CoarseDeGiorgi.local_boundedness`) from
Proposition `p.cg.caccioppoli` (`caccioppoli_inequality`) and Proposition `p.energy.to.sup`
(`energy_to_supremum`), taken as hypotheses with their statements copied verbatim. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.TheoremA

theorem local_boundedness_of_props
    (h81 :
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
                    (eLpNorm v 2 (volume.restrict (originCube ρ₂))) 2)
    (h83 :
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
            LocallyBoundedAbove (originCube 1) u))
    (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ γ : ℝ, 0 < γ ∧
      ((∃ C_A : ℝ, 0 ≤ C_A ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          LocallyBoundedAbove (originCube 1) u ∧
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_A *
            (ENNReal.ofReal (R - ρ)).rpow (-γ) *
            (contrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (4 * paramTheta d p q s t)) *
            eLpNorm (positivePart u) 2 (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) 2
              (volume.restrict (originCube R)) < ⊤)) ∧
      (∀ η : ℝ, 0 < η → η < 2 →
        ∃ C_η : ℝ, 0 ≤ C_η ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          ∀ (ρ R : ℝ), 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let rhs := ENNReal.ofReal C_η *
            (ENNReal.ofReal (R - ρ)).rpow (-(2 * γ / η)) *
            (contrast a ha s t p q hs ht hp.le hq.le).rpow ((d - 1 : ℝ) / (2 * η * paramTheta d p q s t)) *
            eLpNorm (positivePart u) (ENNReal.ofReal η) (volume.restrict (originCube R))
          eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤ rhs ∧
            (R < 1 → eLpNorm (positivePart u) (ENNReal.ofReal η)
              (volume.restrict (originCube R)) < ⊤)))
:= by
  obtain ⟨γ, hγ, C, hC, hA⟩ := theoremA_of_props h81 h83 d _hd p q s t hp hq hs ht _hθ
  have hconv : ∀ C' : ℝ≥0∞, C' < ⊤ → ENNReal.ofReal C'.toReal = C' := fun C' h =>
    ENNReal.ofReal_toReal h.ne
  refine ⟨γ, hγ, ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩, ?_⟩
  · intro a ha hU hL u G hu
    obtain ⟨hlocal, hrest⟩ := hA a ha hU hL u G hu
    refine ⟨hlocal, fun ρ R h1 h2 h3 => ?_⟩
    obtain ⟨hest, hfin⟩ := hrest ρ R h1 h2 h3
    refine ⟨?_, hfin⟩
    rw [hconv C hC]
    exact hest
  · intro η hη hη2
    obtain ⟨Cη, hCη, hB⟩ := corollaryB_of_theoremA d _hd p q s t hp hq hs ht _hθ hγ hC
      (fun a ha hU hL u G hu => hA a ha hU hL u G hu) η hη hη2
    refine ⟨Cη.toReal, ENNReal.toReal_nonneg, ?_⟩
    intro a ha hU hL u G hu ρ R h1 h2 h3
    obtain ⟨_, hrest⟩ := hB a ha hU hL u G hu
    obtain ⟨hest, hfin⟩ := hrest ρ R h1 h2 h3
    refine ⟨?_, hfin⟩
    rw [hconv Cη hCη, show -(2 * γ / η) = -2 * γ / η by ring]
    exact hest

end CoarseDeGiorgi.TheoremA
