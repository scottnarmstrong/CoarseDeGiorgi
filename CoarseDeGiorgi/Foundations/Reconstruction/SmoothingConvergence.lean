module

public import CoarseDeGiorgi.Foundations.Reconstruction.SmoothingTranslation
public import CoarseDeGiorgi.Foundations.Reconstruction.SmoothingAverage
public import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyInputs

/-! # Probability smoothing converges in periodic `L^r` -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
variable {d : ℕ}

/-- Absolute physical scales tend to zero, independently of the cube center. -/
theorem smoothing_auxSide_tendsto (m : ℤ) :
    Tendsto (fun n : ℕ => auxSide (m + n)) atTop (𝓝 0) := by
  have heq (n : ℕ) : auxSide (m + n) = auxSide m * (1 / 3 : ℝ) ^ n := by
    unfold auxSide
    rw [show 1 - (m + (n : ℤ)) = (1 - m) + -(n : ℤ) by omega,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, zpow_natCast, one_div, inv_pow]
  simp_rw [heq]
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (1 / 3 : ℝ) < 1)).const_mul (auxSide m)

/-- The powered norm of a real measurable field is its unnormalized power integral. -/
theorem smoothing_norm_rpow {r : ℝ} (hr : 0 < r) (μ : Measure (Vec d))
    {f : Vec d → ℝ} (hf : Measurable f) :
    eLpNorm f (ENNReal.ofReal r) μ ^ r = ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hr))
    ENNReal.ofReal_ne_top hf.aestronglyMeasurable, ENNReal.toReal_ofReal hr.le,
    ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

/-- Joint measurability of translated powered norms, with the spatial map explicit. -/
theorem smoothing_power_error_measurable (m : ℤ) (t : ℝ) {r : ℝ} (hr : 0 < r)
    {F : Vec d → ℝ} (hFm : Measurable F) : Measurable (fun v : Vec d =>
      eLpNorm (fun x => F (x - t • v) - F x) (ENNReal.ofReal r)
        (volume.restrict (reflectionBox m)) ^ r) := by
  have hs : Measurable (fun p : Vec d × Vec d => p.2 - t • p.1) :=
    (continuous_snd.sub (continuous_fst.const_smul t)).measurable
  have hj : Measurable (fun p : Vec d × Vec d => ‖F (p.2 - t • p.1) - F p.2‖ₑ ^ r) :=
    ((hFm.comp hs).sub (hFm.comp measurable_snd)).enorm.pow_const r
  have hi : Measurable (fun v : Vec d => ∫⁻ x in reflectionBox m, ‖F (x - t • v) - F x‖ₑ ^ r) :=
    hj.lintegral_prod_right'
  have heq : (fun v : Vec d => ∫⁻ x in reflectionBox m, ‖F (x - t • v) - F x‖ₑ ^ r) =
      fun v : Vec d => eLpNorm (fun x => F (x - t • v) - F x) (ENNReal.ofReal r)
        (volume.restrict (reflectionBox m)) ^ r := by
    funext v
    exact (smoothing_norm_rpow hr _
      (f := fun x => F (x - t • v) - F x)
      ((hFm.comp (measurable_id.sub_const _)).sub hFm)).symm
  rw [← heq]
  exact hi


/-- A dominating integrable probability weight controls the translated norm errors. -/
theorem smoothing_translated_errors_tendsto (m : ℤ) {r : ℝ} (hr : 1 < r)
    {F : Vec d → ℝ} (hFm : Measurable F)
    (hF : MemLp F (ENNReal.ofReal r) (volume.restrict (reflectionBox m)))
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) :
    Tendsto (fun n : ℕ => ∫⁻ v : Vec d, ENNReal.ofReal (reconstructionRho v) *
      eLpNorm (fun x => F (x - auxSide (m + n) • v) - F x) (ENNReal.ofReal r)
        (volume.restrict (reflectionBox m)) ^ r) atTop (𝓝 0) := by
  let μ := volume.restrict (reflectionBox (d := d) m)
  let A := eLpNorm F (ENNReal.ofReal r) μ
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hp1 : 1 ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr.le
  have hnorm (n : ℕ) (v : Vec d) :
      eLpNorm (fun x => F (x - auxSide (m + n) • v) - F x) (ENNReal.ofReal r) μ ≤ 2 * A := by
    have htr := eLpNorm_periodicField_add m F hF.aestronglyMeasurable hp
      (-(auxSide (m + n) • v)) (ENNReal.ofReal r)
    have h := eLpNorm_sub_le (f := fun x => F (x - auxSide (m + n) • v)) (g := F)
      (μ := μ) hp1
    have heq : (fun x => F (x - auxSide (m + n) • v)) =
        fun x => F (x + -(auxSide (m + n) • v)) := by ext x; rw [sub_eq_add_neg]
    rw [heq, htr] at h
    change eLpNorm (fun x => F (x + -(auxSide (m + n) • v)) - F x)
      (ENNReal.ofReal r) μ ≤ A + A at h
    simpa only [← sub_eq_add_neg, two_mul] using h
  have hm (n : ℕ) : Measurable (fun v : Vec d => ENNReal.ofReal (reconstructionRho v) *
      eLpNorm (fun x => F (x - auxSide (m + n) • v) - F x) (ENNReal.ofReal r) μ ^ r) :=
    contDiff_reconstructionRho.continuous.measurable.ennreal_ofReal.mul
      (smoothing_power_error_measurable m _ hr0 hFm)
  have hmass : (∫⁻ v : Vec d, ENNReal.ofReal (reconstructionRho v)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_reconstructionRho
      (ae_of_all _ reconstructionRho_nonneg), integral_reconstructionRho, ENNReal.ofReal_one]
  have ht := tendsto_lintegral_of_dominated_convergence
    (μ := (volume : Measure (Vec d)))
    (fun v => ENNReal.ofReal (reconstructionRho v) * (2 * A) ^ r) hm
    (fun n => ae_of_all _ fun v => mul_le_mul_right (ENNReal.rpow_le_rpow (hnorm n v) hr0.le) _)
    (by
      rw [lintegral_mul_const _ contDiff_reconstructionRho.continuous.measurable.ennreal_ofReal,
        hmass, one_mul]
      have hA : A ≠ ∞ := hF.ne
      finiteness)
    (ae_of_all _ fun v => by
      have hshift : Tendsto (fun n : ℕ => -(auxSide (m + n) • v)) atTop (𝓝 (0 : Vec d)) := by
        simpa only [zero_smul, neg_zero] using (smoothing_auxSide_tendsto m).smul_const v |>.neg
      have htr := (smoothing_periodic_translation m hr hF hp).comp hshift
      change Tendsto (fun n : ℕ => eLpNorm
        (fun x => F (x - auxSide (m + n) • v) - F x) (ENNReal.ofReal r) μ) atTop (𝓝 0) at htr
      have hpow := htr.ennrpow_const r
      simp only [ENNReal.zero_rpow_of_pos hr0] at hpow
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (reconstructionRho v)) hpow
          (Or.inr ENNReal.ofReal_ne_top))
  simpa only [lintegral_zero] using ht

/-- The concrete integral smoother converges to every periodic `L^r` field.
There is no assumption concerning fine divergence kernels or gradient tails. -/
theorem smoothing_periodic_average_tendsto (m : ℤ) {r : ℝ} (hr : 1 < r)
    {F : Vec d → ℝ} (hFm : Measurable F) (hFi : IntegrableOn F (reflectionBox m) volume)
    (hF : MemLp F (ENNReal.ofReal r) (volume.restrict (reflectionBox m)))
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun x => (∫ y in reflectionBox m, F y * periodicRho m (auxSide (m + n)) (x - y)) - F x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m))) atTop (𝓝 0) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hb (n : ℕ) := smoothing_norm_error_power_le (auxSide_pos (m + n))
    (assembly_side_le m n) hr hFm hFi hp
  have ht := smoothing_translated_errors_tendsto m hr hFm hF hp
  have hpw := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => bot_le) hb
  have hroot := hpw.ennrpow_const (1 / r)
  simp only [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr0), ← ENNReal.rpow_mul,
    mul_one_div_cancel hr0.ne', ENNReal.rpow_one] at hroot
  exact hroot

end
end CoarseDeGiorgi.Foundations.Reconstruction
