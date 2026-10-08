import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.WeightedEnergy
import CoarseDeGiorgi.Statements.PowerFactor
import CoarseDeGiorgi.Assembly.ParameterDefs

import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.SigmaUpper
import CoarseDeGiorgi.Statements.SigmaLower
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.PowerCaccioppoliInequality

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi

/-- The power Caccioppoli estimate with the exponents `gammaTwoParam` and `sigmaParam` used by the
weak Harnack argument, from Proposition `p.power.caccioppoli` by exponent monotonicity. -/
theorem power_caccioppoli_of_inequality  :
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
                        (volume.restrict (originCube R))).rpow 2 := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C, hC, h⟩ := CoarseDeGiorgi.power_caccioppoli_inequality d hd p q s t hp hq hs ht hθ
  refine ⟨C, hC, fun a ha hrange u G hu hsup ε hε m hm hm0 ρ R hρ hρR hR1 => ?_⟩
  refine (h a ha hrange u G hu hsup ε hε m hm hm0 ρ R hρ hρR hR1).trans ?_
  have hα : 0 < alphaParam t := by
    have : 0 < paramTheta d p q s t := hθ
    unfold paramTheta at this
    have h2 : 0 ≤ (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
      have : 0 < 1 / p + 1 / q := by positivity
      positivity
    unfold alphaParam; nlinarith
  have hγ : gammaLoc p q t ≤ gammaTwoParam (d := d) p q t := by
    unfold gammaLoc gammaTwoParam gammaOneParam alphaParam
    have := le_max_left (1 - t) ((d : ℝ) / (2 * q))
    linarith
  have hσ : sigmaUpper d p s + sigmaLower d q t - t = sigmaParam (d := d) p q s := by
    unfold sigmaUpper sigmaLower sigmaParam; ring
  have hδ : ENNReal.ofReal (R - ρ) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hexp : (-2 * gammaTwoParam (d := d) p q t * alphaParam t / paramTheta d p q s t) ≤
      (-2 * gammaLoc p q t * alphaParam t / paramTheta d p q s t) := by
    apply div_le_div_of_nonneg_right _ hθ.le
    nlinarith
  have hpow := ENNReal.rpow_le_rpow_of_exponent_ge hδ hexp
  rw [hσ]
  gcongr
  exact hpow

end CoarseDeGiorgi
