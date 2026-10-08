import CoarseDeGiorgi.Foundations.Reconstruction.LowestBounds

/-! # Cancellation and translated cancellation for smooth vector kernels -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization

noncomputable section

variable {d : ℕ}

/-- Subtract a smooth kernel's value at the parent-cell center. -/
def kernelCancellation (K : Vec d → Vec d) (y c x : Vec d) : Vec d := K (x - y) - K (x - c)

theorem norm_kernelCancellation_le (K : Vec d → Vec d)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) {M : ℝ}
    (hM : ∀ v, ‖fderiv ℝ K v‖ ≤ M) (y c x : Vec d) :
    ‖kernelCancellation K y c x‖ ≤ M * ‖y - c‖ := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set (Vec d))).norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hK.differentiable (by norm_num) v) (fun v _ => hM v)
    (Set.mem_univ (x - c)) (Set.mem_univ (x - y))
  simpa only [kernelCancellation, show x - y - (x - c) = -(y - c) by abel, norm_neg] using h

theorem fderiv_kernelCancellation (K : Vec d → Vec d)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (y c x : Vec d) :
    fderiv ℝ (kernelCancellation K y c) x =
      fderiv ℝ K (x - y) - fderiv ℝ K (x - c) := by
  have h1 := (hK.differentiable (by norm_num) (x - y)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const y)
  have h2 := (hK.differentiable (by norm_num) (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)
  have hd := h1.sub h2
  change HasFDerivAt (kernelCancellation K y c) _ x at hd
  simpa only [ContinuousLinearMap.comp_id] using hd.fderiv

/-- Two derivatives give a simultaneous parent-length and translation gain. -/
theorem norm_kernelCancellation_translate_sub_le (K : Vec d → Vec d)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) {M : ℝ}
    (hM : ∀ v, ‖fderiv ℝ (fderiv ℝ K) v‖ ≤ M) (y c x u : Vec d) :
    ‖kernelCancellation K y c (x + u) - kernelCancellation K y c x‖ ≤
      M * ‖y - c‖ * ‖u‖ := by
  have hD : ∀ v, ‖fderiv ℝ (kernelCancellation K y c) v‖ ≤ M * ‖y - c‖ := by
    intro v
    rw [fderiv_kernelCancellation K hK]
    have h := (convex_univ : Convex ℝ (Set.univ : Set (Vec d))).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => (hK.fderiv_right (m := 1) (by simp)).differentiable (by norm_num) w)
      (fun w _ => hM w) (Set.mem_univ (v - c)) (Set.mem_univ (v - y))
    simpa only [show v - y - (v - c) = -(y - c) by abel, norm_neg] using h
  have hc : ContDiff ℝ (⊤ : ℕ∞) (kernelCancellation K y c) :=
    (hK.comp (contDiff_id.sub contDiff_const)).sub
      (hK.comp (contDiff_id.sub contDiff_const))
  have h := (convex_univ : Convex ℝ (Set.univ : Set (Vec d))).norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hc.differentiable (by norm_num) v) (fun v _ => hD v)
    (Set.mem_univ x) (Set.mem_univ (x + u))
  simpa only [add_sub_cancel_left] using h

/-- The ordinary translated kernel gains one derivative. -/
theorem norm_kernel_translate_sub_le (K : Vec d → Vec d)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) {M : ℝ}
    (hM : ∀ v, ‖fderiv ℝ K v‖ ≤ M) (x u : Vec d) :
    ‖K (x + u) - K x‖ ≤ M * ‖u‖ := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set (Vec d))).norm_image_sub_le_of_norm_fderiv_le
    (fun v _ => hK.differentiable (by norm_num) v) (fun v _ => hM v)
    (Set.mem_univ x) (Set.mem_univ (x + u))
  simpa only [add_sub_cancel_left] using h

end

end CoarseDeGiorgi.Foundations.Reconstruction
