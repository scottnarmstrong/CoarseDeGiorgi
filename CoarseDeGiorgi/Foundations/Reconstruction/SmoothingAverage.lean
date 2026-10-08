import CoarseDeGiorgi.Foundations.Reconstruction.SmoothingKernel
import CoarseDeGiorgi.Foundations.Reconstruction.SchurIntegral

/-! # Jensen estimate for the actual periodic probability smoother -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section
variable {d : ℕ}

/-- A translated periodic `L¹` field is still integrable on the period box. -/
theorem smoothing_integrable_translate {m : ℤ} {F : Vec d → ℝ}
    (hF : IntegrableOn F (reflectionBox m) volume)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (x : Vec d) :
    IntegrableOn (fun v => F (x - v)) (reflectionBox m) volume := by
  have h := (memLp_one_iff_integrable.mpr hF).comp_measurePreserving
    (measurePreserving_wrapBox_sub m x)
  simp only [Function.comp_def, periodicField_wrapBox m F hp] at h
  exact memLp_one_iff_integrable.mp h

/-- Integrability of the compactly supported physical convolution follows from
periodic `L¹`; global integrability of the periodic field is not assumed. -/
theorem smoothing_integrable_pairing {m : ℤ} {t : ℝ} (ht : 0 < t) (htm : t ≤ auxSide m)
    {F : Vec d → ℝ} (hF : IntegrableOn F (reflectionBox m) volume)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (x : Vec d) :
    Integrable (fun v => scaledRho t v * F (x - v)) volume := by
  have hi := integrableOn_reflectionBox_mul_continuous (smoothing_integrable_translate hF hp x)
    (contDiff_scaledRho t).continuous
  have hi' : IntegrableOn (fun v => scaledRho t v * F (x - v)) (reflectionBox m) volume := by
    simpa only [mul_comm] using hi
  exact hi'.integrable_of_forall_notMem_eq_zero fun v hv => by
    have hz : scaledRho t v = 0 := by
      by_contra hn
      exact hv (smoothing_scaledRho_support ht htm hn)
    rw [hz, zero_mul]

/-- The fixed bump represents the smoothing error, including the constant term. -/
theorem smoothing_error_integral {m : ℤ} {t : ℝ} (ht : 0 < t) (htm : t ≤ auxSide m)
    {F : Vec d → ℝ} (hFm : Measurable F) (hF : IntegrableOn F (reflectionBox m) volume)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (x : Vec d) :
    (∫ y in reflectionBox m, F y * periodicRho m t (x - y)) - F x =
      ∫ v : Vec d, reconstructionRho v * (F (x - t • v) - F x) := by
  rw [smoothing_periodic_integral_eq ht htm hFm hp x]
  have h := smoothing_scaled_integral_eq ht (fun y => F y - F x) x
  have hpair := smoothing_integrable_pairing ht htm hF hp x
  have hconst := (integrable_scaledRho ht (d := d)).mul_const (F x)
  have heq : (∫ v : Vec d, scaledRho t v * (F (x - v) - F x)) =
      (∫ v : Vec d, scaledRho t v * F (x - v)) - F x := by
    simp only [mul_sub]
    rw [integral_sub hpair hconst, integral_mul_const, integral_scaledRho ht, one_mul]
  exact heq.symm.trans h

/-- Jensen for the normalized nonnegative bump. -/
theorem smoothing_error_power_le {m : ℤ} {t r : ℝ} (ht : 0 < t) (htm : t ≤ auxSide m)
    (hr : 1 < r) {F : Vec d → ℝ} (hFm : Measurable F)
    (hF : IntegrableOn F (reflectionBox m) volume)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (x : Vec d) :
    ‖(∫ y in reflectionBox m, F y * periodicRho m t (x - y)) - F x‖ₑ ^ r ≤
      ∫⁻ v : Vec d, ENNReal.ofReal (reconstructionRho v) * ‖F (x - t • v) - F x‖ₑ ^ r := by
  rw [smoothing_error_integral ht htm hFm hF hp x]
  have hm : Measurable (fun v => F (x - t • v) - F x) :=
    (hFm.comp (measurable_const.sub (measurable_id.const_smul t))).sub_const _
  have hnorm : ‖∫ v : Vec d, reconstructionRho v * (F (x - t • v) - F x)‖ₑ ≤
      ∫⁻ v : Vec d, ENNReal.ofReal (reconstructionRho v) * ‖F (x - t • v) - F x‖ₑ := by
    refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
    apply lintegral_congr
    intro v
    rw [enorm_mul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (reconstructionRho_nonneg _)]
  have hmass : (∫⁻ v : Vec d, ENNReal.ofReal (reconstructionRho v)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_reconstructionRho
      (ae_of_all _ reconstructionRho_nonneg), integral_reconstructionRho, ENNReal.ofReal_one]
  have hj := lintegral_weighted_rpow_le volume
    contDiff_reconstructionRho.continuous.measurable.ennreal_ofReal hm.enorm hr
  rw [hmass, ENNReal.one_rpow, one_mul] at hj
  exact (ENNReal.rpow_le_rpow hnorm (zero_lt_one.trans hr).le).trans hj

/-- Tonelli yields the norm error bound by translated norm errors. -/
theorem smoothing_norm_error_power_le {m : ℤ} {t r : ℝ} (ht : 0 < t) (htm : t ≤ auxSide m)
    (hr : 1 < r) {F : Vec d → ℝ} (hFm : Measurable F)
    (hF : IntegrableOn F (reflectionBox m) volume)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) :
    eLpNorm (fun x => (∫ y in reflectionBox m, F y * periodicRho m t (x - y)) - F x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ^ r ≤
      ∫⁻ v : Vec d, ENNReal.ofReal (reconstructionRho v) *
        eLpNorm (fun x => F (x - t • v) - F x) (ENNReal.ofReal r)
          (volume.restrict (reflectionBox m)) ^ r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hprod : Measurable (fun p : Vec d × Vec d =>
      F p.2 * periodicRho m t (p.1 - p.2)) :=
    (hFm.comp measurable_snd).mul
      ((contDiff_periodicRho ht htm).continuous.measurable.comp (measurable_fst.sub measurable_snd))
  have herr : Measurable (fun x => (∫ y in reflectionBox m, F y * periodicRho m t (x - y)) - F x) :=
    hprod.stronglyMeasurable.integral_prod_right'.measurable.sub hFm
  have he (g : Vec d → ℝ) (hg : Measurable g) :
      eLpNorm g (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ^ r =
        ∫⁻ x in reflectionBox m, ‖g x‖ₑ ^ r := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hr0))
      ENNReal.ofReal_ne_top hg.aestronglyMeasurable, ENNReal.toReal_ofReal hr0.le,
      ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
  rw [he _ herr]
  refine (lintegral_mono (smoothing_error_power_le ht htm hr hFm hF hp)).trans_eq ?_
  have herror : Measurable (fun p : Vec d × Vec d =>
      ENNReal.ofReal (reconstructionRho p.2) * ‖F (p.1 - t • p.2) - F p.1‖ₑ ^ r) :=
    (contDiff_reconstructionRho.continuous.measurable.comp measurable_snd).ennreal_ofReal.mul
      (((hFm.comp (measurable_fst.sub (measurable_snd.const_smul t))).sub
        (hFm.comp measurable_fst)).enorm.pow_const r)
  rw [lintegral_lintegral_swap herror.aemeasurable]
  apply lintegral_congr
  intro v
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  exact (he (fun x => F (x - t • v) - F x)
    ((hFm.comp (measurable_id.sub_const (t • v))).sub hFm)).symm

end
end CoarseDeGiorgi.Foundations.Reconstruction
