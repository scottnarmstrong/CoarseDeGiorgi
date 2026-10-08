module

public import CoarseDeGiorgi.Harnack.Log.EnergyLimit
public import CoarseDeGiorgi.Harnack.Log.Membership
public import CoarseDeGiorgi.Harnack.Log.ReplaceMean
public import CoarseDeGiorgi.Harnack.Log.PowerInput
public import CoarseDeGiorgi.Harnack.Log.Centering
public import CoarseDeGiorgi.Harnack.Log.PowerLimit
public import CoarseDeGiorgi.Harnack.Log.GlobalCenter
public import CoarseDeGiorgi.Harnack.LogLimit.EnergyLimit
public import CoarseDeGiorgi.Harnack.LogLimit.OverlapHolder
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.WeightedEnergy

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- Assemble the logarithm membership and limit/centering bridges. The
power-Caccioppoli energy bound and the global fixed-center oscillation are
supplied explicitly to this assembly.
-/
theorem log_estimate_of_fatou_and_center_control {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (_hrange : spatialMomentRange a ha p q s t)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IsWeightedSupersolution a (originCube 1) u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
    (ε : ℝ) (hε : 0 < ε) (C_E C₂ : ℝ≥0∞)
    (_hCE : C_E < ⊤) (_hC₂ : C₂ < ⊤)
    (E : ℕ → ℝ≥0∞)
    (hFatou : weightedEnergy a (originCube (15 / 16 : ℝ))
        (fun x => (u x + ε)⁻¹ • G x) ≤ Filter.liminf E atTop)
    (hPowerBound : ∀ n, E n ≤ C_E *
        upperMoment a ha s p hs (le_of_lt hp))
    (c : ℝ)
    (hGlobalCenter : eLpNorm
        (fun x => Real.log (u x + ε) - c)
        (ENNReal.ofReal (paramR q))
        (volume.restrict (originCube (7 / 8 : ℝ))) ≤
      C₂ * ENNReal.rpow
        (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)) (1 / 2))
    (hMean : eLpNorm
        (fun _ : Vec d => c - volumeAverage (originCube (7 / 8 : ℝ))
          (fun x => Real.log (u x + ε)))
        (ENNReal.ofReal (paramR q))
        (volume.restrict (originCube (7 / 8 : ℝ))) ≤
      C₂ * ENNReal.rpow
        (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)) (1 / 2)) :
    MemH1a a (originCube 1) (fun x => Real.log (u x + ε))
        (fun x => (u x + ε)⁻¹ • G x) ∧
      weightedEnergy a (originCube (15 / 16 : ℝ))
        (fun x => (u x + ε)⁻¹ • G x) ≤
        C_E * upperMoment a ha s p hs (le_of_lt hp) ∧
      IntegrableOn (fun x => Real.log (u x + ε)) (originCube (7 / 8 : ℝ)) ∧
      eLpNorm
        (fun x => Real.log (u x + ε) -
          volumeAverage (originCube (7 / 8 : ℝ)) (fun x => Real.log (u x + ε)))
        (ENNReal.ofReal (paramR q))
        (volume.restrict (originCube (7 / 8 : ℝ))) ≤
      2 * (C₂ * ENNReal.rpow
        (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)) (1 / 2)) := by
  have hmem := log_memH1a hd a ha hu hnonneg ε hε
  have henergy := logEnergy_le_of_fatou_and_power_bound E _ _ hFatou hPowerBound
  have hr : 1 ≤ ENNReal.ofReal (paramR q) := by
    have hrreal : 1 ≤ paramR q := by
      dsimp [paramR]
      have hden : 0 < q + 1 := by linarith
      rw [le_div_iff₀ hden]
      nlinarith
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hrreal
  have hosc := replace_center_by_average (ENNReal.ofReal (paramR q)) hr
    (volumeAverage (originCube (7 / 8 : ℝ)) (fun x => Real.log (u x + ε)))
    c (C₂ * ENNReal.rpow
      (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)) (1 / 2))
    hGlobalCenter hMean
  let : NeZero d := ⟨by omega⟩
  have hcube : originCube (d := d) 1 = auxCube 1 (fun _ : Fin d => 0) := by
    ext x
    simp [originCube, auxCube, sub_self, sub_zero, Int.cast_zero, zero_mul, abs_lt]
  have hV : IsOpenBoundedConvexDomain (originCube (d := d) 1) := by
    rw [hcube]
    exact LowerFractional.auxCube_isOpenBoundedConvexDomain (d := d) 1 (fun _ => 0)
  have hne : (originCube (d := d) 1).Nonempty := by
    rw [hcube]
    exact LowerFractional.auxCube_nonempty (d := d) 1 (fun _ => 0)
  have hlogInt : IntegrableOn (fun x => Real.log (u x + ε)) (originCube (7 / 8 : ℝ)) := by
    apply (Weighted.memH1a_memW11 hV hne ha hmem).1.mono_set
    intro x hx i
    have hx' := hx i
    change -(7 / 8 / 2 : ℝ) < x i ∧ x i < 7 / 8 / 2 at hx'
    constructor <;> norm_num <;> linarith
  exact ⟨hmem, henergy, hlogInt, hosc⟩

/-- Assemble the logarithmic estimate (`l.log.estimate`) from the power-Caccioppoli contract,
the proved (m\to0) energy limit, and the global centering argument. -/
theorem log_estimate_of_power_caccioppoli_input
    (hPower : powerCaccioppoliInputContract) :
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
              weightedEnergy a (originCube (15 / 16 : ℝ))
                (fun x => (u x + ε)⁻¹ • G x) ≤
                C_E * upperMoment a ha s p hs (le_of_lt hp) ∧
              IntegrableOn (fun x => Real.log (u x + ε)) (originCube (7 / 8 : ℝ)) ∧
              eLpNorm (fun x => Real.log (u x + ε) -
                  volumeAverage (originCube (7 / 8 : ℝ)) (fun y => Real.log (u y + ε)))
                (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube (7 / 8 : ℝ))) ≤
                C₂ * (contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                  (1 / 2) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C_E, hCE, hEnergy⟩ :=
    log_energy_bound_of_power_input hPower d hd p q s t hp hq hs ht hθ
  obtain ⟨Ccenter, hCcenter, hCenterAll⟩ := log_global_center_of_energy_bound
    hd p q s t hp hq hs ht hθ C_E hCE
  let C₂ : ℝ≥0∞ := 2 * Ccenter
  have hC₂ : C₂ < ⊤ := by
    simpa [C₂] using
      (ENNReal.mul_lt_top (by norm_num : (2 : ℝ≥0∞) < ⊤) hCcenter)
  refine ⟨C_E, C₂, hCE, hC₂, ?_⟩
  intro a ha hrange u G hnonneg hu ε hε
  have hEnergyData := hEnergy a ha hrange u G hnonneg hu ε hε
  obtain ⟨c, hGlobalCenter, hMean⟩ :=
    hCenterAll a ha hrange u G hu hnonneg ε hε hEnergyData
  let E : ℕ → ℝ≥0∞ := fun _ => C_E * upperMoment a ha s p hs (le_of_lt hp)
  have hFatou : weightedEnergy a (originCube (15 / 16 : ℝ))
      (fun x => (u x + ε)⁻¹ • G x) ≤ Filter.liminf E atTop := by
    rw [show Filter.liminf E atTop =
      C_E * upperMoment a ha s p hs (le_of_lt hp) by simp [E]]
    exact hEnergy a ha hrange u G hnonneg hu ε hε
  have hPowerBound : ∀ n, E n ≤ C_E * upperMoment a ha s p hs (le_of_lt hp) := by
    intro n
    simp [E]
  have hmain := log_estimate_of_fatou_and_center_control hd p q s t hp hq hs ht
    a ha hrange hu hnonneg ε hε C_E Ccenter hCE hCcenter E hFatou hPowerBound c
    hGlobalCenter hMean
  simpa [C₂, mul_assoc] using hmain

end

end CoarseDeGiorgi.Harnack.Log
