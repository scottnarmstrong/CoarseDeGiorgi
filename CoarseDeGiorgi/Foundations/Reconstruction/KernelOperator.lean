module

public import CoarseDeGiorgi.Foundations.Reconstruction.CancellationIntegrals

/-! # Scalar periodic kernel operators and their translation bounds -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Ordinary vector-to-scalar kernel integration over one period. -/
def periodicKernelOperator (m : ℤ) (H : Vec d → Vec d → Vec d)
    (g : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∫ y in reflectionBox m, vecDot (H x y) (g y)

theorem measurable_periodicKernelOperator (m : ℤ) (H : Vec d → Vec d → Vec d)
    (g : Vec d → Vec d) (hH : Measurable (Function.uncurry H)) (hg : Measurable g) :
    Measurable (periodicKernelOperator m H g) :=
  (measurable_vecDot hH (hg.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem periodicKernelOperator_add_period (m : ℤ) (H : Vec d → Vec d → Vec d)
    (hp : ∀ i x y, H (x + (2 * auxSide m) • basisVec i) y = H x y)
    (g : Vec d → Vec d) (i : Fin d) (x : Vec d) :
    periodicKernelOperator m H g (x + (2 * auxSide m) • basisVec i) =
      periodicKernelOperator m H g x := by
  apply integral_congr_ae
  exact ae_of_all _ fun y => congrArg (fun v => vecDot v (g y)) (hp i x y)

/-- Large translations cost at most twice the unshifted operator norm. -/
theorem eLpNorm_periodicKernelOperator_translate_sub_le (m : ℤ)
    (H : Vec d → Vec d → Vec d) (g : Vec d → Vec d)
    (hH : Measurable (Function.uncurry H)) (hg : Measurable g)
    (hp : ∀ i x y, H (x + (2 * auxSide m) • basisVec i) y = H x y)
    (p : ℝ≥0∞) (hp1 : 1 ≤ p) (u : Vec d) :
    eLpNorm (fun x => periodicKernelOperator m H g (x + u) - periodicKernelOperator m H g x)
      p (volume.restrict (reflectionBox m)) ≤
      2 * eLpNorm (periodicKernelOperator m H g) p (volume.restrict (reflectionBox m)) := by
  have hm : AEStronglyMeasurable (periodicKernelOperator m H g)
      (volume.restrict (reflectionBox m)) := (measurable_periodicKernelOperator m H g hH hg).aestronglyMeasurable
  have h := eLpNorm_sub_le (μ := volume.restrict (reflectionBox m)) (f := fun x => periodicKernelOperator m H g (x + u))
    (g := periodicKernelOperator m H g) hp1
  rw [eLpNorm_periodicField_add m _ hm (periodicKernelOperator_add_period m H hp g)] at h
  exact h.trans_eq (two_mul _).symm

/-- A pointwise vector bound gives the Schur bound with the ordinary box volume. -/
theorem eLpNorm_periodicKernelOperator_le_const (m : ℤ)
    (H : Vec d → Vec d → Vec d) (g : Vec d → Vec d)
    (hH : Measurable (Function.uncurry H)) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x y, ‖H x y‖ ≤ B) {r : ℝ} (hr : 1 < r) :
    eLpNorm (periodicKernelOperator m H g) (ENNReal.ofReal r)
      (volume.restrict (reflectionBox m)) ≤
      (ENNReal.ofReal (Real.sqrt (d : ℝ) * B) * ENNReal.ofReal ((2 * auxSide m) ^ d)) *
        eLpNorm (fun y => euclidNorm (g y)) (ENNReal.ofReal r)
          (volume.restrict (reflectionBox m)) := by
  have hb (x y : Vec d) : ENNReal.ofReal (euclidNorm (H x y)) ≤
      ENNReal.ofReal (Real.sqrt (d : ℝ) * B) :=
    ENNReal.ofReal_le_ofReal ((Euclid.eNorm2_le_sqrt_mul_norm _).trans
      (mul_le_mul_of_nonneg_left (hB x y) (Real.sqrt_nonneg _)))
  have hmass := volume_reflectionBox (d := d) m
  apply eLpNorm_kernelOperator_le _ _ H g hH hg _ _ hr
  · intro x
    calc
      _ ≤ ∫⁻ _y in reflectionBox m, ENNReal.ofReal (Real.sqrt (d : ℝ) * B) :=
        lintegral_mono (hb x)
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, hmass]
  · intro y
    calc
      _ ≤ ∫⁻ _x in reflectionBox m, ENNReal.ofReal (Real.sqrt (d : ℝ) * B) :=
        lintegral_mono (fun x => hb x y)
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, hmass]

end

end CoarseDeGiorgi.Foundations.Reconstruction
