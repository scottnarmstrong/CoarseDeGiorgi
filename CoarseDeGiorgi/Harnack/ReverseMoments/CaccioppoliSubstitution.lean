module

public import CoarseDeGiorgi.Harnack.ReverseMoments.InnerLocalization
public import CoarseDeGiorgi.Statements.PowerFactor
public import CoarseDeGiorgi.Assembly.ParameterDefs

@[expose] public section

namespace CoarseDeGiorgi.Harnack.ReverseMoments

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The source inner Sobolev estimate with the exact power-Caccioppoli
statement supplied as its explicit input. The energy term is replaced by the
Caccioppoli right-hand side at the midpoint radius. -/
theorem signed_power_inner_bound_of_power_caccioppoli
    (hPowerCaccioppoli :
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
                        (eLpNorm (fun x => (u x + ε) ^ m)
                          (ENNReal.ofReal (paramR q))
                          (volume.restrict (originCube R))).rpow 2)
    {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ C₀ C₁ : ℝ≥0∞, 0 < C₀ ∧ C₀ < ⊤ ∧ C₁ < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε →
            ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
              ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                eLpNorm (fun x => (u x + ε) ^ m)
                    (ENNReal.ofReal (rStarParam (d := d) q t))
                    (volume.restrict (originCube ρ)) ≤
                  C₀ * ENNReal.ofReal (((R - ρ) / 2) ^
                      (-gammaOneParam (d := d) q t)) *
                    ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
                        (C₁ * (ENNReal.ofReal ((R - ρ) / 2)).rpow
                              (-2 * gammaTwoParam (d := d) p q t * alphaParam t /
                                paramTheta d p q s t) *
                            upperMoment a ha s p hs hp.le *
                            ENNReal.ofReal (powerFactor m ^ 2) *
                            (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                              contrast a ha s t p q hs ht hp.le hq.le).rpow
                              (sigmaParam (d := d) p q s / paramTheta d p q s t) *
                            (eLpNorm (fun x => (u x + ε) ^ m)
                              (ENNReal.ofReal (paramR q))
                              (volume.restrict (originCube R))).rpow 2) ^
                          (1 / 2 : ℝ) +
                      eLpNorm (fun x => (u x + ε) ^ m)
                        (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube R))) := by
  obtain ⟨C₀, hC₀, hC₀top, hSobolev⟩ :=
    signed_power_inner_sobolev hd hp hq hs ht hθ
  obtain ⟨C₁, hC₁top, hPower⟩ :=
    hPowerCaccioppoli d hd p q s t hp hq hs ht hθ
  refine ⟨C₀, C₁, hC₀, hC₀top, hC₁top, ?_⟩
  intro a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  let ρ' : ℝ := (ρ + R) / 2
  have hρ'lo : 1 / 2 ≤ ρ' := by dsimp [ρ']; linarith
  have hρ'hi : ρ' < R := by dsimp [ρ']; linarith
  have hmid : R - ρ' = (R - ρ) / 2 := by dsimp [ρ']; ring
  have hnext := hPower a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ' R
    hρ'lo hρ'hi hR
  have hSob := hSobolev a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  have hLpMono : eLpNorm (fun x => (u x + ε) ^ m)
      (ENNReal.ofReal (paramR q)) (volume.restrict (originCube ρ')) ≤
      eLpNorm (fun x => (u x + ε) ^ m)
        (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R)) := by
    apply eLpNorm_mono_measure
    exact Measure.restrict_mono (Assembly.caccioppoli_cube_mono hρ'hi.le) le_rfl
  let Ebound : ℝ≥0∞ := C₁ * (ENNReal.ofReal (R - ρ')).rpow
      (-2 * gammaTwoParam (d := d) p q t * alphaParam t / paramTheta d p q s t) *
      upperMoment a ha s p hs hp.le * ENNReal.ofReal (powerFactor m ^ 2) *
      (1 + ENNReal.ofReal (powerFactor m ^ 2) *
        contrast a ha s t p q hs ht hp.le hq.le).rpow
          (sigmaParam (d := d) p q s / paramTheta d p q s t) *
      (eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
        (volume.restrict (originCube R))).rpow 2
  have hE : weightedEnergy a (originCube ρ')
        (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤ Ebound := by
    simpa only [Ebound] using hnext
  have hroot : (weightedEnergy a (originCube ρ')
        (fun x => (m * (u x + ε) ^ (m - 1)) • G x)).rpow (1 / 2 : ℝ) ≤
      Ebound.rpow (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hE (by norm_num)
  have hroot' : weightedEnergy a (originCube ρ')
        (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ^ (1 / 2 : ℝ) ≤
      Ebound ^ (1 / 2 : ℝ) := hroot
  calc
    _ ≤ C₀ * ENNReal.ofReal (((R - ρ) / 2) ^
          (-gammaOneParam (d := d) q t)) *
        ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) * Ebound ^
            (1 / 2 : ℝ) + eLpNorm (fun x => (u x + ε) ^ m)
              (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))) := by
      calc
        _ ≤ C₀ * ENNReal.ofReal (((R - ρ) / 2) ^
              (-gammaOneParam (d := d) q t)) *
            ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
                (weightedEnergy a (originCube ρ')
                  (fun x => (m * (u x + ε) ^ (m - 1)) • G x)) ^ (1 / 2 : ℝ) +
              eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube ρ'))) := hSob
        _ ≤ _ := by
          gcongr
    _ = _ := by simp only [Ebound, hmid]

end

end CoarseDeGiorgi.Harnack.ReverseMoments
