import CoarseDeGiorgi.Harnack.Log.Estimate
import CoarseDeGiorgi.PowerCacc.HarnackForm

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

theorem log_estimate_proved :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C_E C₂ : ℝ≥0∞, C_E < ⊤ ∧ C₂ < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε →
              MemH1a a (originCube 1) (fun x => Real.log (u x + ε))
                  (fun x => (u x + ε)⁻¹ • G x) ∧
              weightedEnergy a (originCube (15 / 16))
                  (fun x => (u x + ε)⁻¹ • G x) ≤
                C_E * upperMoment a ha s p hs (le_of_lt hp) ∧
              IntegrableOn (fun x => Real.log (u x + ε)) (originCube (7 / 8)) ∧
              eLpNorm (fun x => Real.log (u x + ε) -
                  volumeAverage (originCube (7 / 8)) (fun y => Real.log (u y + ε)))
                (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube (7 / 8))) ≤
                C₂ * (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                  (1 / 2) := by
  exact Harnack.Log.log_estimate_of_power_caccioppoli_input
    (CoarseDeGiorgi.power_caccioppoli_of_inequality)

end CoarseDeGiorgi
