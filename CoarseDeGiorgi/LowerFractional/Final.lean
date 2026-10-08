module

public import CoarseDeGiorgi.Statements.LowerFractionalBound
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.H1aWeightedNorm

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable section

theorem lower_fractional_proved :
    ∀ d : ℕ, 3 ≤ d → ∀ q t : ℝ, (hq : 1 < q) → (ht : 0 < t) →
      ∃ C : ℝ, 0 < C ∧
        ∀ p s : ℝ, (hp : 1 < p) → (hs : 0 < s) →
          ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
            spatialMomentRange a ha p q s t →
            ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (G : Vec d → Vec d),
              closure (auxCube m z) ⊆ originCube 1 → MemH1a a (auxCube m z) w G →
              fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
                ENNReal.ofReal C *
                  ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2) *
                  ENNReal.rpow (weightedEnergy a (auxCube m z) G) (1 / 2) :=
  by
    intro d hd q t hq ht
    obtain ⟨C, hC, hbound⟩ := lower_fractional_bound d hd q t hq ht
    refine ⟨C, hC, ?_⟩
    intro p s hp hs a ha hrange m z w G hQ hw
    exact hbound p s hp hs a ha hrange m z w G (subset_closure.trans hQ) hw

end
end CoarseDeGiorgi
