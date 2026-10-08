import CoarseDeGiorgi.Foundations.Reconstruction.FineKernelScaling
import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicReflection

/-! # Smooth periodic continuation by coordinate wrapping

The seam neighborhoods are zero because the support lies strictly inside
its fundamental box. No infinite periodization sum is used.
-/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

variable {d : ℕ}

theorem wrapCoordinate_sub_periodShift (m : ℤ) (u t : ℝ) :
    wrapCoordinate m (u - (t - wrapCoordinate m t)) = wrapCoordinate m u := by
  unfold wrapCoordinate
  rw [self_sub_toIcoMod, toIcoMod_sub_zsmul]

theorem wrapBox_sub_periodShift (m : ℤ) (y x : Vec d) :
    wrapBox m (y - (x - wrapBox m x)) = wrapBox m y := by
  funext i
  exact wrapCoordinate_sub_periodShift m (y i) (x i)

theorem wrapCoordinate_mem_Ico (m : ℤ) (t : ℝ) :
    wrapCoordinate m t ∈ Set.Ico (-auxSide m) (auxSide m) := by
  have h := toIcoMod_mem_Ico (mul_pos (by norm_num : (0 : ℝ) < 2) (auxSide_pos m))
    (-auxSide m) t
  simpa only [wrapCoordinate, show -auxSide m + 2 * auxSide m = auxSide m by ring] using h

/-- Near a wrapping seam, the wrapped coordinate stays away from the kernel support. -/
theorem abs_wrapCoordinate_gt_half {m : ℤ} {t : ℝ}
    (ht : |t + auxSide m| < auxSide m / 4) :
    auxSide m / 2 < |wrapCoordinate m t| := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp ht
  have hl := auxSide_pos m
  by_cases h : -auxSide m ≤ t
  · have heq : wrapCoordinate m t = t := by
      apply (toIcoMod_eq_self _).mpr
      exact ⟨h, by linarith⟩
    rw [heq, abs_of_neg (by linarith)]
    linarith
  · have heq : wrapCoordinate m (t + 2 * auxSide m) = t + 2 * auxSide m := by
      apply (toIcoMod_eq_self _).mpr
      exact ⟨by linarith, by linarith⟩
    rw [wrapCoordinate_add_period] at heq
    rw [heq, abs_of_pos (by linarith)]
    linarith

/-- On the closed fundamental box, wrapping preserves the field locally, including seams. -/
theorem eventuallyEq_comp_wrapBox_fundamental {E : Type*} [NormedAddCommGroup E]
    (m : ℤ) (F : Vec d → E) (hz : ∀ v, auxSide m / 2 < ‖v‖ → F v = 0)
    (w : Vec d) (hw : ∀ i, w i ∈ Set.Ico (-auxSide m) (auxSide m)) :
    (fun y => F (wrapBox m y)) =ᶠ[𝓝 w] F := by
  have hopen : IsOpen (reflectionBox (d := d) m) := by
    simp only [reflectionBox, ← Set.iInter_ofPred]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).abs continuous_const
  by_cases hi : ∀ i, -auxSide m < w i
  · have hwbox : w ∈ reflectionBox m := fun i => abs_lt.mpr ⟨hi i, (hw i).2⟩
    have heq : (fun y => F (wrapBox m y)) =ᶠ[𝓝 w] F := by
      filter_upwards [hopen.mem_nhds hwbox] with y hy
      rw [wrapBox_eq_self m hy]
    exact heq
  · push Not at hi
    obtain ⟨i, hi⟩ := hi
    have hwi : w i = -auxSide m := le_antisymm hi (hw i).1
    have heq : (fun y => F (wrapBox m y)) =ᶠ[𝓝 w] F := by
      filter_upwards [Metric.ball_mem_nhds w (div_pos (auxSide_pos m) (by norm_num : (0 : ℝ) < 4))]
        with y hy
      have hc : |y i + auxSide m| < auxSide m / 4 := by
        have hn := norm_le_pi_norm (y - w) i
        rw [Real.norm_eq_abs, Pi.sub_apply, hwi, sub_neg_eq_add] at hn
        exact hn.trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)
      have hyi : auxSide m / 2 < |y i| := by
        have hh := (abs_lt.mp hc).2
        rw [abs_of_neg (by linarith [auxSide_pos m])]
        linarith [auxSide_pos m]
      rw [hz _ ((abs_wrapCoordinate_gt_half hc).trans_le
        (by simpa only [wrapBox, Real.norm_eq_abs] using norm_le_pi_norm (wrapBox m y) i)),
        hz _ (hyi.trans_le (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y i))]
    exact heq

/-- Wrapping a smooth field supported in the central half-box is smooth everywhere. -/
theorem contDiff_comp_wrapBox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℤ) (F : Vec d → E) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hz : ∀ v, auxSide m / 2 < ‖v‖ → F v = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => F (wrapBox m x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let c := x - wrapBox m x
  have hl := hF.contDiffAt.congr_of_eventuallyEq
    (eventuallyEq_comp_wrapBox_fundamental m F hz (wrapBox m x)
      (fun i => wrapCoordinate_mem_Ico m (x i)))
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Vec d => y - c) x :=
    contDiffAt_id.sub contDiffAt_const
  have hxc : x - c = wrapBox m x := by dsimp only [c]; abel
  rw [← hxc] at hl
  have h := hl.comp x hc
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F (wrapBox m (y - c))) x at h
  simpa only [c, wrapBox_sub_periodShift] using h

/-- The wrapped derivative is the precursor derivative at the wrapped point. -/
theorem fderiv_comp_wrapBox {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℤ) (F : Vec d → E) (hF : Differentiable ℝ F)
    (hz : ∀ v, auxSide m / 2 < ‖v‖ → F v = 0) (x : Vec d) :
    fderiv ℝ (fun y => F (wrapBox m y)) x = fderiv ℝ F (wrapBox m x) := by
  let c := x - wrapBox m x
  have hxc : x - c = wrapBox m x := by dsimp only [c]; abel
  have hl := eventuallyEq_comp_wrapBox_fundamental m F hz (wrapBox m x)
    (fun i => wrapCoordinate_mem_Ico m (x i))
  rw [← hxc] at hl
  have ht : Tendsto (fun y : Vec d => y - c) (𝓝 x) (𝓝 (x - c)) :=
    (continuous_id.sub continuous_const).continuousAt
  have heq := hl.comp_tendsto ht
  change (fun y => F (wrapBox m (y - c))) =ᶠ[𝓝 x] (fun y => F (y - c)) at heq
  simp only [c, wrapBox_sub_periodShift] at heq
  rw [heq.fderiv_eq]
  have h := (hF (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c)
  have hd : fderiv ℝ (fun y => F (y - c)) x =
      (fderiv ℝ F (x - c)).comp (ContinuousLinearMap.id ℝ (Vec d)) := h.fderiv
  simpa only [hxc, ContinuousLinearMap.comp_id] using hd

/-- Fine periodic kernels are obtained directly by wrapping their compact precursors. -/
def periodicFineKernel (m : ℤ) (h : ℝ) (x : Vec d) : Vec d := fineKernel h (wrapBox m x)

theorem contDiff_periodicFineKernel {m : ℤ} {h : ℝ} (hh : 0 < h)
    (hsmall : 3 * h ≤ auxSide m) :
    ContDiff ℝ (⊤ : ℕ∞) (periodicFineKernel (d := d) m h) := by
  apply contDiff_comp_wrapBox m (fineKernel h) (contDiff_fineKernel hh)
  intro v hv
  exact fineKernel_eq_zero_of_norm_gt hh (lt_of_le_of_lt (by linarith) hv)

theorem periodicFineKernel_add_period (m : ℤ) (h : ℝ) (i : Fin d) (x : Vec d) :
    periodicFineKernel m h (x + (2 * auxSide m) • basisVec i) = periodicFineKernel m h x := by
  unfold periodicFineKernel
  rw [wrapBox_add_period_basisVec]

end

end CoarseDeGiorgi.Foundations.Reconstruction
