import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicMeasure
import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyBlocks

/-! # The concrete periodic smoother as a physical-space probability average -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Set

noncomputable section
variable {d : ℕ}

/-- The scaled probability density is supported strictly inside the period box. -/
theorem smoothing_scaledRho_support {m : ℤ} {t : ℝ} (ht : 0 < t) (htm : t ≤ auxSide m) :
    Function.support (scaledRho (d := d) t) ⊆ reflectionBox m := by
  intro v hv i
  have hb := support_scaledRho_subset ht hv
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  have hi : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  exact (hi.trans hb).trans_lt (by linarith [auxSide_pos m])

/-- Wrapping either endpoint changes a periodic difference kernel by a lattice period. -/
theorem smoothing_periodic_sub_wrap (m : ℤ) (K : Vec d → ℝ)
    (hp : ∀ i x, K (x + (2 * auxSide m) • basisVec i) = K x) (x y : Vec d) :
    K (x - wrapBox m y) = K (x - y) := by
  have hw := wrapBox_sub_periodShift m (x - wrapBox m y) y
  rw [show x - wrapBox m y - (y - wrapBox m y) = x - y by abel] at hw
  rw [← periodicField_wrapBox m K hp (x - wrapBox m y), ← hw,
    periodicField_wrapBox m K hp (x - y)]

/-- Periodic integration unfolded to a compactly supported physical kernel.
It uses only the scalar probability bump, not the fine divergence kernels. -/
theorem smoothing_periodic_integral_eq {m : ℤ} {t : ℝ} (ht : 0 < t)
    (htm : t ≤ auxSide m) {F : Vec d → ℝ} (hF : Measurable F)
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) (x : Vec d) :
    (∫ y in reflectionBox m, F y * periodicRho m t (x - y)) =
      ∫ v : Vec d, scaledRho t v * F (x - v) := by
  let G : Vec d → ℝ := fun y => F y * periodicRho m t (x - y)
  have hG : Measurable G := hF.mul
    ((contDiff_periodicRho ht htm).continuous.measurable.comp (measurable_const.sub measurable_id))
  have hm := measurePreserving_wrapBox_sub m x
  have hi := integral_map hm.measurable.aemeasurable
    (show AEStronglyMeasurable G (Measure.map (fun v => wrapBox m (x - v))
      (volume.restrict (reflectionBox m))) from by rw [hm.map_eq]; exact hG.aestronglyMeasurable)
  rw [hm.map_eq] at hi
  calc
    _ = ∫ v in reflectionBox m, G (wrapBox m (x - v)) := hi
    _ = ∫ v in reflectionBox m, periodicRho m t v * F (x - v) := by
      apply integral_congr_ae
      exact ae_of_all _ fun v => by
        dsimp only [G]
        rw [periodicField_wrapBox m F hp,
          smoothing_periodic_sub_wrap m (periodicRho m t) (periodicRho_add_period m t),
          sub_sub_cancel, mul_comm]
    _ = ∫ v in reflectionBox m, scaledRho t v * F (x - v) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (assembly_reflectionBox_measurable m)] with v hv
      rw [periodicRho, wrapBox_eq_self m hv]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => by
      have hz : scaledRho t v = 0 := by
        by_contra hn
        exact hv (smoothing_scaledRho_support ht htm hn)
      rw [hz, zero_mul]

/-- The physical average at scale t is the fixed probability bump applied at t v. -/
theorem smoothing_scaled_integral_eq {t : ℝ} (ht : 0 < t) (F : Vec d → ℝ) (x : Vec d) :
    (∫ v : Vec d, scaledRho t v * F (x - v)) =
      ∫ v : Vec d, reconstructionRho v * F (x - t • v) := by
  have h := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun v => scaledRho t v * F (x - v)) t
  rw [Module.finrank_fin_fun, abs_of_pos (inv_pos.mpr (pow_pos ht _)), smul_eq_mul] at h
  have heq : (∫ v : Vec d, scaledRho t (t • v) * F (x - t • v)) =
      (t ^ d)⁻¹ * ∫ v : Vec d, reconstructionRho v * F (x - t • v) := by
    simp only [scaledRho, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, mul_assoc]
    rw [integral_const_mul]
  rw [heq] at h
  have hpos := pow_pos ht d
  exact (mul_left_cancel₀ (inv_ne_zero hpos.ne') h).symm

end
end CoarseDeGiorgi.Foundations.Reconstruction
