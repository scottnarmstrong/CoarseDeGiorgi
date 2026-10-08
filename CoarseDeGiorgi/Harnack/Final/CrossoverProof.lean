import CoarseDeGiorgi.Harnack.CrossoverFinal.ConditionalAssembly
import CoarseDeGiorgi.Harnack.Iterations.UniformSmallIterations
import CoarseDeGiorgi.Statements.LogEstimate
import CoarseDeGiorgi.PowerCacc.HarnackForm

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

theorem crossover_proved :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ c : ℝ, 0 < c ∧ c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) ∧
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
                ∫⁻ x in originCube (3 / 4), ENNReal.ofReal ((u x + ε) ^ (-b))) ≤ C := by
  have hPower : Harnack.Log.powerCaccioppoliInputContract :=
    (CoarseDeGiorgi.power_caccioppoli_of_inequality)
  have hLog : Harnack.CrossoverFinal.logEstimateInputContract :=
    CoarseDeGiorgi.log_estimate
  have hIterations : ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C₃ γ₆ : ℝ, 1 ≤ C₃ ∧ 0 < γ₆ ∧
        ∀ c : ℝ, 0 < c →
        c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) →
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube (d := d) 1) a)
          (_hrange : spatialMomentRange a ha p q s t)
          (u : Vec d → ℝ) (G : Vec d → Vec d)
          (_hu : IsWeightedSupersolution a (originCube (d := d) 1) u G)
          (_hnonneg : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), 0 ≤ u x)
          (ε : ℝ) (_hε : 0 < ε),
        let pC : ℝ := crossoverExponent c a ha s t p q hs ht
          (le_of_lt hp) (le_of_lt hq)
        (∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
          eLpNorm (fun x => (u x + ε) ^ pC) 1
              (volume.restrict (originCube ρ)) ≤
            (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
              eLpNorm (fun x => (u x + ε) ^ pC)
                (ENNReal.ofReal b) (volume.restrict (originCube R))) ∧
        (∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
          eLpNorm (fun x => (u x + ε) ^ (-pC)) 1
              (volume.restrict (originCube ρ)) ≤
            (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
              eLpNorm (fun x => (u x + ε) ^ (-pC))
                (ENNReal.ofReal b) (volume.restrict (originCube R))) := by
    intro d hd p q s t hp hq hs ht hθ
    exact Harnack.Iterations.uniform_small_signed_iterations_of_power_caccioppoli
      hPower hd hp hq hs ht hθ
  exact Harnack.CrossoverFinal.crossover_of_iterations_and_log_estimate_input
    hLog hIterations

end CoarseDeGiorgi
