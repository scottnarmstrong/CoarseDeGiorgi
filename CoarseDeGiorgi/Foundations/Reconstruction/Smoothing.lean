module

public import CoarseDeGiorgi.Foundations.Reconstruction.SmoothingConvergence

/-! # Smoothing estimate for fractional reconstruction -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
variable {d : ℕ}

/-- Reflection preserves finite-exponent membership, with no gradient premise. -/
theorem smoothing_memLp_reflected {m : ℤ} {z : Fin d → ℤ} {w : Vec d → ℝ}
    {r : ℝ} (hr : 0 < r) (hwm : Measurable w)
    (hw : MemLp w (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z))) :
    MemLp (reflectedScalar m z w) (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) := by
  have hRm : Measurable (reflectedScalar m z w) := hwm.comp
    (measurable_const.add (measurable_pi_iff.mpr fun i => (continuous_apply i).abs.measurable))
  have hnorm : (∫⁻ x in CoarseDeGiorgi.auxCube m z, ‖w x‖ₑ ^ r) ≠ ∞ := by
    rw [← smoothing_norm_rpow hr _ hwm]
    have hfin := hw.ne
    finiteness
  have hl := lintegral_reflectedScalar m z (fun x => ‖w x‖ₑ ^ r)
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top hRm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hr.le]
  change (∫⁻ x in reflectionBox m,
    ‖w (auxLower m z + fun i => |x i|)‖ₑ ^ r) ^ (1 / r) < ∞
  rw [hl]
  have hnorm' : (∫⁻ x in auxCube m z, ‖w x‖ₑ ^ r) ≠ ∞ := by
    simpa only [auxCube_eq_statement] using hnorm
  finiteness

/-- Integrable representatives give the same reflected scalar a.e. -/
theorem smoothing_reflected_congr_ae {m : ℤ} {z : Fin d → ℤ} {w w' : Vec d → ℝ}
    (hw : IntegrableOn w (CoarseDeGiorgi.auxCube m z) volume)
    (hw' : IntegrableOn w' (CoarseDeGiorgi.auxCube m z) volume)
    (heq : w =ᵐ[volume.restrict (CoarseDeGiorgi.auxCube m z)] w') :
    reflectedScalar m z w =ᵐ[volume.restrict (reflectionBox m)] reflectedScalar m z w' := by
  have hi : IntegrableOn (reflectedScalar m z (w - w')) (reflectionBox m) volume :=
    integrableOn_reflectedScalar (hw.sub hw')
  have hl := lintegral_reflectedScalar m z (fun y => ‖w y - w' y‖ₑ)
  have hz : (∫⁻ y in auxCube m z, ‖w y - w' y‖ₑ) = 0 := by
    rw [auxCube_eq_statement]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [heq] with y hy
    simp only [hy, sub_self, enorm_zero, Pi.zero_apply]
  rw [hz, mul_zero] at hl
  have hzero : (∫⁻ x in reflectionBox m, ‖reflectedScalar m z (w - w') x‖ₑ) = 0 := hl
  have hae := (lintegral_eq_zero_iff' hi.aestronglyMeasurable.enorm).mp hzero
  filter_upwards [hae] with x hx
  change ‖w (auxLower m z + fun i => |x i|) - w' (auxLower m z + fun i => |x i|)‖ₑ = 0 at hx
  exact sub_eq_zero.mp (enorm_eq_zero.mp hx)

/-- First prove the exact input for a globally measurable representative. -/
theorem smoothing_smoothAverage_tendsto_of_measurable {r : ℝ} (hr : 1 < r)
    (m : ℤ) (z : Fin d → ℤ) {w : Vec d → ℝ} (hwm : Measurable w)
    (hw : IntegrableOn w (CoarseDeGiorgi.auxCube m z) volume)
    (hmem : MemLp w (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z))) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun x => smoothAverage m (auxSide (m + n)) z w x - reflectedScalar m z w x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m))) atTop (𝓝 0) := by
  let F := periodicReflectedScalar m z w
  have hFm : Measurable F := by
    apply (hwm.comp (measurable_const.add
      (measurable_pi_iff.mpr fun i => (continuous_apply i).abs.measurable))).comp
        (measurable_wrapBox m)
  have hbox : F =ᵐ[volume.restrict (reflectionBox m)] reflectedScalar m z w := by
    filter_upwards [ae_restrict_mem (assembly_reflectionBox_measurable m)] with x hx
    exact periodicReflectedScalar_eq_on_box m z w hx
  have hFi : IntegrableOn F (reflectionBox m) volume :=
    (integrableOn_reflectedScalar hw).congr hbox.symm
  have hFmem : MemLp F (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) :=
    (smoothing_memLp_reflected (zero_lt_one.trans hr) hwm hmem).ae_eq hbox.symm
  have ht := smoothing_periodic_average_tendsto m hr hFm hFi hFmem
    (periodicReflectedScalar_add_period m z w)
  have hconv (n : ℕ) (x : Vec d) :
      smoothAverage m (auxSide (m + n)) z w x =
        ∫ y in reflectionBox m, F y * periodicRho m (auxSide (m + n)) (x - y) := by
    apply integral_congr_ae
    filter_upwards [hbox] with y hy
    rw [hy]
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [hbox] with x hx
  rw [hconv n x, hx]

/-- `AssemblySmoothingConvergence`, for every dimension and every integrable representative.
It needs no kernel or tail-bound hypothesis. -/
theorem assemblySmoothingConvergence {d : ℕ} {r : ℝ} (hr : 1 < r) :
    AssemblySmoothingConvergence d r := by
  intro m z w hw hmem
  let w' := hw.aestronglyMeasurable.mk w
  have hwm : Measurable w' := hw.aestronglyMeasurable.measurable_mk
  have heq : w =ᵐ[volume.restrict (CoarseDeGiorgi.auxCube m z)] w' :=
    hw.aestronglyMeasurable.ae_eq_mk
  have hw' : IntegrableOn w' (CoarseDeGiorgi.auxCube m z) volume := hw.congr heq
  have hmem' := hmem.ae_eq heq
  have hR := smoothing_reflected_congr_ae hw hw' heq
  have ht := smoothing_smoothAverage_tendsto_of_measurable hr m z hwm hw' hmem'
  have hS (t : ℝ) (x : Vec d) : smoothAverage m t z w x = smoothAverage m t z w' x := by
    apply integral_congr_ae
    filter_upwards [hR] with y hy
    rw [hy]
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [hR] with x hx
  rw [hS, hx]

end
end CoarseDeGiorgi.Foundations.Reconstruction
