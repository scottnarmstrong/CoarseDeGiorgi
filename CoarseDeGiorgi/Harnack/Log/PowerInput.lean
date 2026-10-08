import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.WeightedEnergy
import CoarseDeGiorgi.Statements.PowerFactor
import CoarseDeGiorgi.Assembly.ParameterDefs
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.UpperMoment

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The exact `power_caccioppoli` statement, repeated locally as an
explicit input contract. -/
abbrev powerCaccioppoliInputContract : Prop :=
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε →
              ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
                ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                  weightedEnergy a (originCube ρ)
                    (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                    C * (ENNReal.ofReal (R - ρ)).rpow
                        (-2 * gammaTwoParam (d := d) p q t * alphaParam t /
                          paramTheta d p q s t) *
                      upperMoment a ha s p hs (le_of_lt hp) *
                      ENNReal.ofReal (powerFactor m ^ 2) *
                      (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                        contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                          (sigmaParam (d := d) p q s / paramTheta d p q s t) *
                      (eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube R))).rpow 2

end

end CoarseDeGiorgi.Harnack.Log
