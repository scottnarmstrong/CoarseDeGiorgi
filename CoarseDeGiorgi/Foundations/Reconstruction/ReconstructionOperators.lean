import CoarseDeGiorgi.Foundations.Reconstruction.ReconstructionKernels
import CoarseDeGiorgi.Foundations.Reconstruction.OperatorDifference
import CoarseDeGiorgi.Foundations.Reconstruction.IncrementPairing

/-! # Uniform operator bounds at each reconstruction scale -/
namespace CoarseDeGiorgi.Foundations.Reconstruction
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ}

/-- A scale-normalized kernel bound, with fine-scale support, controls both Schur masses. -/
theorem eLpNorm_reconstruction_supported_le (m : ℤ) (j : ℕ)
    (H : Vec d → Vec d → Vec d) (hH : Measurable (Function.uncurry H))
    (g : Vec d → Vec d) (hg : Measurable g) {B r : ℝ} (hB : 0 ≤ B) (hr : 1 < r)
    (hb : ∀ x y, ‖H x y‖ ≤ B * (auxSide (m + j) ^ d)⁻¹)
    (hs : ∀ n, j = n + 1 → ∀ x y, 3 * auxSide (m + j) < ‖wrapBox m (x - y)‖ → H x y = 0) :
    eLpNorm (periodicKernelOperator m H g) (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤
      ENNReal.ofReal (Real.sqrt (d : ℝ) * B * (6 : ℝ) ^ d) *
        eLpNorm (fun y => euclidNorm (g y)) (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) := by
  have hh := auxSide_pos (m + j)
  cases j with
  | zero =>
    have h := eLpNorm_periodicKernelOperator_le_const m H g hH hg hb hr
    apply h.trans
    gcongr
    simp only [Nat.cast_zero, add_zero] at hh ⊢
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = Real.sqrt (d : ℝ) * B * (2 : ℝ) ^ d := by
        rw [mul_pow]; field_simp
      _ ≤ _ := by gcongr; norm_num
  | succ n =>
    have hpoint (x y : Vec d) : ENNReal.ofReal (euclidNorm (H x y)) ≤
        ENNReal.ofReal (Real.sqrt (d : ℝ) * B) * periodicEnvelope m (auxSide (m + (n + 1 : ℕ))) (x - y) := by
      by_cases hx : ‖wrapBox m (x - y)‖ ≤ 3 * auxSide (m + (n + 1 : ℕ))
      · rw [periodicEnvelope_eq_of_norm_le m _ hx, ← ENNReal.ofReal_inv_of_pos (pow_pos hh d),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal ((Euclid.eNorm2_le_sqrt_mul_norm _).trans
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x y) (Real.sqrt_nonneg _)))
      · rw [hs n rfl x y (lt_of_not_ge hx), euclidNorm_eq_eNorm2, Euclid.eNorm2_zero, ENNReal.ofReal_zero]
        exact bot_le
    obtain ⟨hrow, hcol⟩ := lintegral_enveloped_kernel_le hh H _ hpoint
    rw [← ENNReal.ofReal_mul (by positivity)] at hrow hcol
    exact eLpNorm_kernelOperator_le _ _ H g hH hg hrow hcol hr

/-- Fine support also controls a small translation of the unsubtracted kernel. -/
theorem reconstructionKernel_translate_support (m : ℤ) (n : ℕ) (x y u : Vec d)
    (hu : ‖u‖ ≤ auxSide (m + (n + 1 : ℕ)))
    (hx : 3 * auxSide (m + (n + 1 : ℕ)) < ‖wrapBox m (x - y)‖) :
    reconstructionKernel m (n + 1) (x + u - y) = 0 := by
  have hh := auxSide_pos (m + (n + 1 : ℕ))
  have hsmall := reconstruction_fine_side_small m n
  apply periodicFineKernel_eq_zero_of_norm_gt hh
  have h := norm_wrapBox_gt_of_norm_gt (m := m)
    (R := 3 * auxSide (m + (n + 1 : ℕ)) / 2) (x - y) u
    (hu.trans (by linarith only [hsmall, hh])) (by linarith only [hu, hx, hh])
  simpa only [show x - y + u = x + u - y by abel] using h

end
end CoarseDeGiorgi.Foundations.Reconstruction
