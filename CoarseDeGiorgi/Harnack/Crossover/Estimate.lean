module

public import CoarseDeGiorgi.Harnack.Final.CrossoverProof
public import CoarseDeGiorgi.Harnack.CrossoverFinal.Parameters

/-! The crossover estimate for positive and negative moments. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Harnack.Crossover

theorem crossover_estimate_proved :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ c : ℝ, 0 < c ∧ c ≤ paramR q / 4 ∧
        ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε →
              let b := crossoverExponent c a ha s t p q hs ht
                (le_of_lt hp) (le_of_lt hq)
              ((volume (originCube (d := d) (3 / 4)))⁻¹ *
                ∫⁻ x in originCube (3 / 4), ENNReal.ofReal ((u x + ε) ^ b)) *
              ((volume (originCube (d := d) (3 / 4)))⁻¹ *
                ∫⁻ x in originCube (3 / 4), ENNReal.ofReal ((u x + ε) ^ (-b))) ≤ C
:=
  by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨c, hc, hcap, C, hC, hbound⟩ :=
    CoarseDeGiorgi.crossover_proved d hd p q s t hp hq hs ht hθ
  have hχ := Harnack.CrossoverFinal.chiParam_gt_one_of_source_parameters
    hd p q s t hp hq hs ht hθ
  have hr : 0 ≤ paramR q := by
    unfold paramR
    exact div_nonneg (by linarith only [hq]) (by linarith only [hq])
  have hden : (4 : ℝ) ≤ 16 * chiParam d q t := by linarith only [hχ]
  refine ⟨c, hc, ?_, C, hC, hbound⟩
  exact (hcap.trans (min_le_right _ _)).trans
    (div_le_div_of_nonneg_left hr (by norm_num) hden)

end CoarseDeGiorgi.Harnack.Crossover
