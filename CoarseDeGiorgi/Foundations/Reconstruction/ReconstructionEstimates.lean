import CoarseDeGiorgi.Foundations.Reconstruction.ReconstructionOperators

/-! # The kernel and parent-subtracted kernel have the same translation modulus -/
namespace CoarseDeGiorgi.Foundations.Reconstruction
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section
variable {d : ℕ}

/-- Small-translation and periodic large-translation bounds combine into the exact minimum. -/
theorem eLpNorm_periodic_operator_min_le (m : ℤ) {h : ℝ} (hh : 0 < h)
    (H : Vec d → Vec d → Vec d) (g : Vec d → Vec d)
    (hH : Measurable (Function.uncurry H)) (hg : Measurable g)
    (hp : ∀ i x y, H (x + (2 * auxSide m) • basisVec i) y = H x y)
    {r : ℝ} (hr : 1 < r) {C : ℝ≥0∞}
    (h0 : eLpNorm (periodicKernelOperator m H g) (ENNReal.ofReal r)
      (volume.restrict (reflectionBox m)) ≤ C)
    (h1 : ∀ u : Vec d, ‖u‖ ≤ h →
      eLpNorm (fun x => periodicKernelOperator m H g (x + u) - periodicKernelOperator m H g x)
        (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤ ENNReal.ofReal (‖u‖ / h) * C)
    (u : Vec d) :
    eLpNorm (fun x => periodicKernelOperator m H g (x + u) - periodicKernelOperator m H g x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤
        2 * ENNReal.ofReal (min 1 (euclidNorm u / h)) * C := by
  have hp1 : 1 ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr.le
  by_cases hu : ‖u‖ ≤ h
  · apply (h1 u hu).trans
    apply mul_le_mul_of_nonneg_right _ bot_le
    calc
      _ ≤ ENNReal.ofReal (min 1 (euclidNorm u / h)) := ENNReal.ofReal_le_ofReal
        (le_min ((div_le_one hh).mpr hu) (div_le_div_of_nonneg_right (Euclid.norm_le_eNorm2 u) hh.le))
      _ ≤ 2 * ENNReal.ofReal (min 1 (euclidNorm u / h)) := by
        calc _ = 1 * _ := (one_mul _).symm
             _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ≥0∞) ≤ 2) bot_le
  · have he : 1 ≤ euclidNorm u / h := (le_div_iff₀ hh).mpr
      (by rw [one_mul, euclidNorm_eq_eNorm2]; exact (le_of_not_ge hu).trans (Euclid.norm_le_eNorm2 u))
    rw [min_eq_left he, ENNReal.ofReal_one, mul_one]
    exact (eLpNorm_periodicKernelOperator_translate_sub_le m H g hH hg hp _ hp1 u).trans
      (mul_le_mul_of_nonneg_left h0 bot_le)

/-- A bounded jointly measurable kernel can use its pointwise translated kernel estimate. -/
theorem eLpNorm_operator_small_of_supported (m : ℤ) (j : ℕ)
    (H : Vec d → Vec d → Vec d) (hH : Measurable (Function.uncurry H))
    (g : Vec d → Vec d) (hg : Measurable g) (hgi : IntegrableOn g (reflectionBox m) volume)
    {M B r : ℝ} (hM : ∀ x y, ‖H x y‖ ≤ M) (hB : 0 ≤ B) (hr : 1 < r)
    (u : Vec d)
    (hb : ∀ x y, ‖H (x + u) y - H x y‖ ≤ B * (auxSide (m + j) ^ d)⁻¹)
    (hs : ∀ n, j = n + 1 → ∀ x y, 3 * auxSide (m + j) < ‖wrapBox m (x - y)‖ →
      H (x + u) y - H x y = 0) :
    eLpNorm (fun x => periodicKernelOperator m H g (x + u) - periodicKernelOperator m H g x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤
      ENNReal.ofReal (Real.sqrt (d : ℝ) * B * (6 : ℝ) ^ d) *
        eLpNorm (fun y => euclidNorm (g y)) (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) := by
  have hm : Measurable (Function.uncurry (fun x y => H (x + u) y)) :=
    hH.comp ((measurable_fst.add_const u).prodMk measurable_snd)
  have heq : (fun x => periodicKernelOperator m H g (x + u) - periodicKernelOperator m H g x) =
      periodicKernelOperator m (fun x y => H (x + u) y - H x y) g := by
    funext x
    exact periodicKernelOperator_sub m _ H hm hH g hgi (fun x y => hM (x + u) y) hM x
  rw [heq]
  exact eLpNorm_reconstruction_supported_le m j _ (hm.sub hH) g hg hB hr hb hs

/-- Base action on a reflected average: side length times its Euclidean Lʳ size. -/
theorem reconstruction_operator_bounds (m : ℤ) (j : ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr : 1 < r)
    (h0 : ∀ v : Vec d, ‖reconstructionKernel m j v‖ ≤ A * auxSide (m + j) * (auxSide (m + j) ^ d)⁻¹)
    (h1 : ∀ v : Vec d, ‖fderiv ℝ (reconstructionKernel m j) v‖ ≤ A * (auxSide (m + j) ^ d)⁻¹)
    (g : Vec d → Vec d) (hg : Measurable g) (hgi : IntegrableOn g (reflectionBox m) volume) :
    let C := ENNReal.ofReal (Real.sqrt (d : ℝ) * A * auxSide (m + j) * (6 : ℝ) ^ d) *
      eLpNorm (fun y => euclidNorm (g y)) (ENNReal.ofReal r) (volume.restrict (reflectionBox m))
    eLpNorm (periodicKernelOperator m (fun x y => reconstructionKernel m j (x - y)) g)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤ C ∧
    ∀ u, eLpNorm (fun x => periodicKernelOperator m (fun x y => reconstructionKernel m j (x - y)) g (x + u) -
      periodicKernelOperator m (fun x y => reconstructionKernel m j (x - y)) g x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤
        2 * ENNReal.ofReal (min 1 (euclidNorm u / auxSide (m + j))) * C := by
  have hh := auxSide_pos (m + j)
  have hK := contDiff_reconstructionKernel (d := d) m j
  have hm : Measurable (fun p : Vec d × Vec d => reconstructionKernel m j (p.1 - p.2)) :=
    hK.continuous.measurable.comp (measurable_fst.sub measurable_snd)
  have hs (n : ℕ) (hj : j = n + 1) (x y : Vec d)
      (hx : 3 * auxSide (m + j) < ‖wrapBox m (x - y)‖) : reconstructionKernel m j (x - y) = 0 := by
    subst j
    exact periodicFineKernel_eq_zero_of_norm_gt hh (by linarith only [hx, hh])
  have hb := eLpNorm_reconstruction_supported_le m j _ hm g hg (by positivity : 0 ≤ A * auxSide (m + j)) hr
    (fun x y => h0 (x - y)) hs
  simp only [← mul_assoc] at hb
  refine ⟨hb, eLpNorm_periodic_operator_min_le m hh (fun x y => reconstructionKernel m j (x - y)) g hm hg ?_ hr hb ?_⟩
  · intro i x y
    rw [show x + (2 * auxSide m) • basisVec i - y = (x - y) + (2 * auxSide m) • basisVec i by abel]
    exact reconstructionKernel_add_period m j i (x - y)
  · intro u hu
    have h := eLpNorm_operator_small_of_supported m j _ hm g hg hgi (fun x y => h0 (x - y))
      (by positivity : 0 ≤ A * ‖u‖) hr u
      (fun x y => (by simpa only [show x + u - y = (x - y) + u by abel, mul_right_comm] using
        norm_kernel_translate_sub_le _ hK h1 (x - y) u)) ?_
    · apply h.trans_eq
      conv_rhs => rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      apply congrArg ENNReal.ofReal
      field_simp
    · intro n hj x y hx
      subst j
      rw [reconstructionKernel_translate_support m n x y u hu hx, hs n rfl x y hx, sub_self]

/-- Parent subtraction replaces the kernel side length by the parent radius. -/
theorem reconstruction_cancellation_operator_bounds (m : ℤ) (j : ℕ) {A s r : ℝ}
    (hA : 0 ≤ A) (hs : 0 ≤ s) (hsh : s ≤ auxSide (m + j) / 2) (hr : 1 < r)
    (h1 : ∀ v : Vec d, ‖fderiv ℝ (reconstructionKernel m j) v‖ ≤ A * (auxSide (m + j) ^ d)⁻¹)
    (h2 : ∀ v : Vec d, ‖fderiv ℝ (fderiv ℝ (reconstructionKernel m j)) v‖ ≤
      A * (auxSide (m + j) ^ d)⁻¹ * (auxSide (m + j))⁻¹)
    (c : Vec d → Vec d) (hcm : Measurable c) (hc : ∀ y, ‖y - c y‖ ≤ s)
    (g : Vec d → Vec d) (hg : Measurable g) (hgi : IntegrableOn g (reflectionBox m) volume) :
    let H := fun x y => kernelCancellation (reconstructionKernel m j) y (c y) x
    let C := ENNReal.ofReal (Real.sqrt (d : ℝ) * A * s * (6 : ℝ) ^ d) *
      eLpNorm (fun y => euclidNorm (g y)) (ENNReal.ofReal r) (volume.restrict (reflectionBox m))
    eLpNorm (periodicKernelOperator m H g) (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤ C ∧
    ∀ u, eLpNorm (fun x => periodicKernelOperator m H g (x + u) - periodicKernelOperator m H g x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤
        2 * ENNReal.ofReal (min 1 (euclidNorm u / auxSide (m + j))) * C := by
  have hh := auxSide_pos (m + j)
  have hK := contDiff_reconstructionKernel (d := d) m j
  let H := fun x y => kernelCancellation (reconstructionKernel m j) y (c y) x
  have hm : Measurable (Function.uncurry H) :=
    (hK.continuous.measurable.comp (measurable_fst.sub measurable_snd)).sub
      (hK.continuous.measurable.comp (measurable_fst.sub (hcm.comp measurable_snd)))
  have hbound (x y : Vec d) : ‖H x y‖ ≤ A * s * (auxSide (m + j) ^ d)⁻¹ :=
    (norm_kernelCancellation_le _ hK h1 y (c y) x).trans
      ((mul_le_mul_of_nonneg_left (hc y) (by positivity)).trans_eq (by ring))
  have hsupport (n : ℕ) (hj : j = n + 1) (x y : Vec d)
      (hx : 3 * auxSide (m + j) < ‖wrapBox m (x - y)‖) : H x y = 0 := by
    subst j
    exact kernelCancellation_periodicFine_eq_zero hh (reconstruction_fine_side_small m n)
      y (c y) x ((hc y).trans hsh) hx
  have hb := eLpNorm_reconstruction_supported_le m j H hm g hg (mul_nonneg hA hs) hr hbound hsupport
  simp only [← mul_assoc] at hb
  refine ⟨hb, eLpNorm_periodic_operator_min_le m hh H g hm hg ?_ hr hb ?_⟩
  · intro i x y
    dsimp only [H, kernelCancellation]
    rw [show x + (2 * auxSide m) • basisVec i - y = (x - y) + (2 * auxSide m) • basisVec i by abel,
      show x + (2 * auxSide m) • basisVec i - c y = (x - c y) + (2 * auxSide m) • basisVec i by abel,
      reconstructionKernel_add_period, reconstructionKernel_add_period]
  · intro u hu
    have h := eLpNorm_operator_small_of_supported m j H hm g hg hgi hbound
      (by positivity : 0 ≤ A * s * (‖u‖ / auxSide (m + j))) hr u
      (fun x y => (norm_kernelCancellation_translate_sub_le _ hK h2 y (c y) x u).trans
        (by calc
              _ ≤ (A * (auxSide (m + j) ^ d)⁻¹ * (auxSide (m + j))⁻¹) * s * ‖u‖ := by gcongr; exact hc y
              _ = _ := by rw [div_eq_mul_inv]; ring)) ?_
    · apply h.trans_eq
      conv_rhs => rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      apply congrArg ENNReal.ofReal
      ring
    · intro n hj x y hx
      subst j
      rw [show H (x + u) y = 0 from kernelCancellation_periodicFine_translate_eq_zero hh
        (reconstruction_fine_side_small m n) y (c y) x u ((hc y).trans hsh) hu hx,
        hsupport n rfl x y hx, sub_self]

end
end CoarseDeGiorgi.Foundations.Reconstruction
