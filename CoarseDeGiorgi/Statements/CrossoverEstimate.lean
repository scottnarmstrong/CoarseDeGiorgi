import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.CrossoverExponent

import CoarseDeGiorgi.Harnack.Crossover.Estimate
open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

/-- Lemma `l.crossover` with `e.small.exponent`: the exponent is `p_* = c/√(1+Θ)` (`crossoverExponent`) for a constant
`c ∈ (0, r/4]` depending only on `d,p,q,s,t`; the paper takes `c := min {r/4, 1/(1+C)}`, with `C` the constant of `e.log.mean.zero`, and `p_* = c/√Θ`. -/
theorem crossover_estimate :
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
  CoarseDeGiorgi.Harnack.Crossover.crossover_estimate_proved

end CoarseDeGiorgi
