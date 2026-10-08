import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicEnvelope
import CoarseDeGiorgi.Foundations.Reconstruction.CancellationJets

/-! # Fine periodic cancellation: support and quantitative envelope bounds -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Wrapped fine kernels have the same support radius as their compact precursors. -/
theorem periodicFineKernel_eq_zero_of_norm_gt {m : ℤ} {h : ℝ} (hh : 0 < h)
    {v : Vec d} (hv : 3 * h / 2 < ‖wrapBox m v‖) : periodicFineKernel m h v = 0 :=
  fineKernel_eq_zero_of_norm_gt hh hv

/-- Both parent-subtracted values vanish outside the enlarged envelope. -/
theorem kernelCancellation_periodicFine_eq_zero {m : ℤ} {h : ℝ} (hh : 0 < h)
    (hsmall : 3 * h ≤ auxSide m) (y c x : Vec d)
    (hc : ‖y - c‖ ≤ h / 2) (hx : 3 * h < ‖wrapBox m (x - y)‖) :
    kernelCancellation (periodicFineKernel m h) y c x = 0 := by
  have hshift : x - y + (y - c) = x - c := by abel
  have hs : ‖y - c‖ ≤ auxSide m := hc.trans (by linarith)
  have hv := norm_wrapBox_gt_of_norm_gt (m := m) (R := 3 * h / 2) (x - y) (y - c) hs
    (by linarith)
  rw [hshift] at hv
  rw [kernelCancellation, periodicFineKernel_eq_zero_of_norm_gt hh (by linarith),
    periodicFineKernel_eq_zero_of_norm_gt hh hv, sub_self]

/-- Small translations still fit inside the same envelope, centered at `x-y`. -/
theorem kernelCancellation_periodicFine_translate_eq_zero {m : ℤ} {h : ℝ} (hh : 0 < h)
    (hsmall : 3 * h ≤ auxSide m) (y c x u : Vec d)
    (hc : ‖y - c‖ ≤ h / 2) (hu : ‖u‖ ≤ h)
    (hx : 3 * h < ‖wrapBox m (x - y)‖) :
    kernelCancellation (periodicFineKernel m h) y c (x + u) = 0 := by
  have huc : ‖u + (y - c)‖ ≤ 3 * h / 2 := (norm_add_le _ _).trans (by linarith)
  have h1 := norm_wrapBox_gt_of_norm_gt (m := m) (R := 3 * h / 2) (x - y) u
    (hu.trans (by linarith)) (by linarith)
  have h2 := norm_wrapBox_gt_of_norm_gt (m := m) (R := 3 * h / 2) (x - y) (u + (y - c))
    (huc.trans (by linarith)) (by linarith)
  rw [show x - y + u = x + u - y by abel] at h1
  rw [show x - y + (u + (y - c)) = x + u - c by abel] at h2
  rw [kernelCancellation, periodicFineKernel_eq_zero_of_norm_gt hh h1,
    periodicFineKernel_eq_zero_of_norm_gt hh h2, sub_self]

end

end CoarseDeGiorgi.Foundations.Reconstruction
