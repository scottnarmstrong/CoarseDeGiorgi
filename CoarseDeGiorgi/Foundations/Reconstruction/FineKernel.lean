module

public import CoarseDeGiorgi.Foundations.Reconstruction.ScaledBump
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Euclidean-space precursors of the fine vector kernels

All spatial bounds in this file use the sup norm on `Vec d`.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Integrand in the physical-space divergence inverse. -/
def fineKernelIntegrand (t : ℝ) (v : Vec d) : Vec d := scaledRho t v • (t⁻¹ • v)

/-- Fine kernel at physical length `h`, before periodic continuation. -/
def fineKernel (h : ℝ) (v : Vec d) : Vec d :=
  ∫ t in Set.Icc h (3 * h), fineKernelIntegrand t v ∂volume

theorem continuousOn_fineKernelIntegrand {h : ℝ} (hh : 0 < h) (v : Vec d) :
    ContinuousOn (fun t => fineKernelIntegrand t v) (Set.Icc h (3 * h)) := by
  intro t ht
  have ht0 : 0 < t := hh.trans_le ht.1
  have hinv := continuousAt_id.inv₀ ht0.ne'
  have hr : ContinuousAt (fun s : ℝ => scaledRho s v) t := by
    change ContinuousAt (fun s : ℝ => (s ^ d)⁻¹ * reconstructionRho (s⁻¹ • v)) t
    apply ((continuousAt_id.pow d).inv₀ (pow_ne_zero _ ht0.ne')).mul
    exact contDiff_reconstructionRho.continuous.continuousAt.comp
      (hinv.smul continuousAt_const)
  exact (hr.smul (hinv.smul continuousAt_const)).continuousWithinAt

theorem integrableOn_fineKernelIntegrand {h : ℝ} (hh : 0 < h) (v : Vec d) :
    IntegrableOn (fun t => fineKernelIntegrand t v) (Set.Icc h (3 * h)) volume :=
  (continuousOn_fineKernelIntegrand hh v).integrableOn_Icc

theorem fineKernelIntegrand_eq_zero_of_norm_gt {t : ℝ} (ht : 0 < t) {v : Vec d}
    (hv : t / 2 < ‖v‖) : fineKernelIntegrand t v = 0 := by
  rw [fineKernelIntegrand, scaledRho_eq_zero_of_norm_gt ht hv, zero_smul]

theorem fineKernel_eq_zero_of_norm_gt {h : ℝ} (hh : 0 < h) {v : Vec d}
    (hv : 3 * h / 2 < ‖v‖) : fineKernel h v = 0 := by
  unfold fineKernel
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact fineKernelIntegrand_eq_zero_of_norm_gt (hh.trans_le ht.1)
    (lt_of_le_of_lt (by linarith [ht.2]) hv)

theorem support_fineKernel_subset {h : ℝ} (hh : 0 < h) :
    Function.support (fineKernel (d := d) h) ⊆ Metric.closedBall 0 (3 * h / 2) := by
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hv (fineKernel_eq_zero_of_norm_gt hh (lt_of_not_ge h))

end

end CoarseDeGiorgi.Foundations.Reconstruction
