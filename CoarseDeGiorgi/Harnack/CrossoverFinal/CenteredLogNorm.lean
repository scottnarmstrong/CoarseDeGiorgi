import CoarseDeGiorgi.Harnack.CrossoverFinal.LogCenter
import CoarseDeGiorgi.Harnack.Crossover.Normalization
import CoarseDeGiorgi.Harnack.LogLimit.OverlapHolder
import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas

namespace CoarseDeGiorgi.Harnack.CrossoverFinal

open Homogenization MeasureTheory
open Filter
open scoped ENNReal

noncomputable section

private theorem eLpNorm_one_eq_ofReal_integral_abs {d : ℕ}
    {μ : Measure (Vec d)} {f : Vec d → ℝ} (hf : Integrable f μ) :
    eLpNorm f 1 μ = ENNReal.ofReal (∫ x, |f x| ∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  simpa only [← ofReal_norm, Real.norm_eq_abs] using
    (ofReal_integral_eq_lintegral_ofReal hf.norm
      (Eventually.of_forall fun x => norm_nonneg (f x))).symm

/-- The log-estimate input gives the L¹ norm bounds for the two centered
weights required by the Bombieri lemma `l.bombieri`. -/
theorem centered_weight_log_eLpNorm_le_one_of_log_estimate
    (hLog : logEstimateInputContract) {d : ℕ}
    (hd : 3 ≤ d) (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hs : 0 < s) (ht : 0 < t) (hθ : 0 < paramTheta d p q s t)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t)
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hnonneg : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), 0 ≤ u x)
    (hu : IsWeightedSupersolution a (originCube (d := d) 1) u G)
    (ε : ℝ) (hε : 0 < ε)
    (c : ℝ) (hc : 0 < c) (hcc : c * C₂ ≤ 1)
    (hcenter : volumeAverage (originCube (d := d) (7 / 8))
      (fun x => |Real.log (u x + ε) -
        volumeAverage (originCube (d := d) (7 / 8))
          (fun y => Real.log (u y + ε))|) ≤
        C₂ * Real.sqrt
          (contrast a ha s t p q hs ht hp.le hq.le).toReal) :
    let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
    eLpNorm (fun x => Real.log
      (Harnack.Crossover.centeredWeight (originCube (d := d) (7 / 8))
        (fun y => u y + ε) pC x)) 1
      (volume.restrict (originCube (d := d) (7 / 8))) ≤ ENNReal.ofReal 1 ∧
    eLpNorm (fun x => Real.log
      (Harnack.Crossover.centeredWeightInv (originCube (d := d) (7 / 8))
        (fun y => u y + ε) pC x)) 1
      (volume.restrict (originCube (d := d) (7 / 8))) ≤ ENNReal.ofReal 1 := by
  let V := originCube (d := d) (7 / 8)
  let U : Vec d → ℝ := fun x => u x + ε
  let θ := contrast a ha s t p q hs ht hp.le hq.le
  let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
  have hθtop : θ < ⊤ := by
    dsimp [θ]
    exact Harnack.Crossover.contrast_lt_top_of_spatialMomentRange
      a ha s t p q hs ht hp.le hq.le hrange
  have hUpos : ∀ᵐ x ∂(volume.restrict V), 0 < U x := by
    have hmeasure : volume.restrict V ≤ volume.restrict (originCube (d := d) 1) :=
      Measure.restrict_mono
        (Harnack.Scalar.originCube_subset_of_le_one (by norm_num)) le_rfl
    filter_upwards [ae_mono hmeasure hnonneg] with x hx
    dsimp [U]
    linarith
  have hlogAll := hLog d hd p q s t hp hq hs ht hθ
  obtain ⟨_, _, _, _, hLogFor⟩ := hlogAll
  have hlogU : IntegrableOn (fun x => Real.log (U x)) V := by
    have h := hLogFor a ha hrange u G hnonneg hu ε hε
    exact h.2.2.1
  have hVtop : volume V < ⊤ := lt_of_le_of_lt
    (Harnack.Scalar.volume_originCube_le_one (d := d) (by norm_num))
    ENNReal.one_lt_top
  have hVpos : 0 < (volume V).toReal := by
    exact ENNReal.toReal_pos
      (Harnack.Scalar.volume_originCube_pos (d := d) (by norm_num)).ne' hVtop.ne
  have hVle : (volume V).toReal ≤ 1 := by
    apply ENNReal.toReal_mono ENNReal.one_ne_top
    exact Harnack.Scalar.volume_originCube_le_one (d := d) (by norm_num)
  let μ := volumeAverage V (fun y => Real.log (U y))
  have hcenterInt : Integrable
      (fun x => Real.log (U x) - μ) (volume.restrict V) := by
    change IntegrableOn (fun x => Real.log (U x) - μ) V
    have hconst : IntegrableOn (fun _ : Vec d => μ) V :=
      integrableOn_const hVtop.ne
    exact hlogU.sub hconst
  have hlogPlusAE : (fun x => Real.log
      (Harnack.Crossover.centeredWeight V U pC x)) =ᵐ[volume.restrict V]
      (fun x => pC * (Real.log (U x) - μ)) := by
    filter_upwards [hUpos] with x hx
    simpa [μ] using Harnack.Crossover.centeredWeight_log V U pC hx
  have hlogMinusAE : (fun x => Real.log
      (Harnack.Crossover.centeredWeightInv V U pC x)) =ᵐ[volume.restrict V]
      (fun x => -pC * (Real.log (U x) - μ)) := by
    filter_upwards [hUpos] with x hx
    simpa [μ] using Harnack.Crossover.centeredWeightInv_log V U pC hx
  have hlogPlusInt : Integrable (fun x => Real.log
      (Harnack.Crossover.centeredWeight V U pC x))
      (volume.restrict V) := by
    have hmul : Integrable (fun x => pC * (Real.log (U x) - μ))
        (volume.restrict V) := by
      simpa [smul_eq_mul, mul_comm] using hcenterInt.const_mul pC
    exact hmul.congr hlogPlusAE.symm
  have hlogMinusInt : Integrable (fun x => Real.log
      (Harnack.Crossover.centeredWeightInv V U pC x))
      (volume.restrict V) := by
    have hmul : Integrable (fun x => -pC * (Real.log (U x) - μ))
        (volume.restrict V) := by
      simpa [smul_eq_mul, mul_comm] using hcenterInt.const_mul (-pC)
    exact hmul.congr hlogMinusAE.symm
  have hnormAvg := Harnack.Crossover.centeredWeight_log_average_bound
    V U pC c C₂ a ha s t p q hs ht hp.le hq.le hθtop hc.le hC₂
    rfl hcc (by simpa [V, U] using hcenter) hUpos
  have hlogPlusIntegral :
      (∫ x in V, |Real.log
        (Harnack.Crossover.centeredWeight V U pC x)|) ≤ (volume V).toReal := by
    have hcancel : (∫ x in V, |Real.log
        (Harnack.Crossover.centeredWeight V U pC x)|) =
        (volume V).toReal * volumeAverage V (fun x => |Real.log
          (Harnack.Crossover.centeredWeight V U pC x)|) := by
      rw [show volumeAverage V (fun x => |Real.log
        (Harnack.Crossover.centeredWeight V U pC x)|) =
          (volume V).toReal⁻¹ * (∫ x in V, |Real.log
            (Harnack.Crossover.centeredWeight V U pC x)|) by rfl]
      field_simp [ne_of_gt hVpos]
    calc
      _ = (volume V).toReal * volumeAverage V (fun x => |Real.log
          (Harnack.Crossover.centeredWeight V U pC x)|) := hcancel
      _ ≤ (volume V).toReal * 1 :=
        mul_le_mul_of_nonneg_left hnormAvg.1 hVpos.le
      _ = (volume V).toReal := by ring
  have hlogMinusIntegral :
      (∫ x in V, |Real.log
        (Harnack.Crossover.centeredWeightInv V U pC x)|) ≤ (volume V).toReal := by
    have hcancel : (∫ x in V, |Real.log
        (Harnack.Crossover.centeredWeightInv V U pC x)|) =
        (volume V).toReal * volumeAverage V (fun x => |Real.log
          (Harnack.Crossover.centeredWeightInv V U pC x)|) := by
      rw [show volumeAverage V (fun x => |Real.log
        (Harnack.Crossover.centeredWeightInv V U pC x)|) =
          (volume V).toReal⁻¹ * (∫ x in V, |Real.log
            (Harnack.Crossover.centeredWeightInv V U pC x)|) by rfl]
      field_simp [ne_of_gt hVpos]
    calc
      _ = (volume V).toReal * volumeAverage V (fun x => |Real.log
          (Harnack.Crossover.centeredWeightInv V U pC x)|) := hcancel
      _ ≤ (volume V).toReal * 1 :=
        mul_le_mul_of_nonneg_left hnormAvg.2 hVpos.le
      _ = (volume V).toReal := by ring
  have hlogPlusIntegralOne := hlogPlusIntegral.trans hVle
  have hlogMinusIntegralOne := hlogMinusIntegral.trans hVle
  constructor
  · rw [eLpNorm_one_eq_ofReal_integral_abs hlogPlusInt]
    exact ENNReal.ofReal_le_ofReal hlogPlusIntegralOne
  · rw [eLpNorm_one_eq_ofReal_integral_abs hlogMinusInt]
    exact ENNReal.ofReal_le_ofReal hlogMinusIntegralOne

end

end CoarseDeGiorgi.Harnack.CrossoverFinal
