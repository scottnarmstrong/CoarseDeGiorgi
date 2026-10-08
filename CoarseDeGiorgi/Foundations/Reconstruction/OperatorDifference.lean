module

public import CoarseDeGiorgi.Foundations.Reconstruction.KernelOperator
public import CoarseDeGiorgi.Foundations.Reconstruction.KernelApproximation

/-! # Integrability and subtraction for bounded kernel operators -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

theorem integrable_periodicKernelOperator_integrand (m : ℤ)
    (H : Vec d → Vec d → Vec d) (hH : Measurable (Function.uncurry H))
    (g : Vec d → Vec d) (hg : IntegrableOn g (reflectionBox m) volume)
    {M : ℝ} (hM : ∀ x y, ‖H x y‖ ≤ M) (x : Vec d) :
    IntegrableOn (fun y => vecDot (H x y) (g y)) (reflectionBox m) volume := by
  have hcoord : AEStronglyMeasurable (fun y => H x y) (volume.restrict (reflectionBox m)) :=
    (hH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hpair : AEStronglyMeasurable (fun y => vecDot (H x y) (g y))
      (volume.restrict (reflectionBox m)) := by
    have heq : (fun y => vecDot (H x y) (g y)) =
        ∑ i : Fin d, fun y => H x y i * g y i := by
      ext y
      simp only [vecDot, Finset.sum_apply]
    rw [heq]
    exact Finset.aestronglyMeasurable_sum _ fun i _ =>
      ((continuous_apply i).comp_aestronglyMeasurable hcoord).mul
        (hg.eval i).aestronglyMeasurable
  apply (hg.norm.const_mul ((d : ℝ) * M)).mono' hpair
  exact ae_of_all _ fun y => (norm_vecDot_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hM x y) (Nat.cast_nonneg d)) (norm_nonneg _))

/-- Subtraction of two bounded kernel operators agrees with pointwise kernel subtraction. -/
theorem periodicKernelOperator_sub (m : ℤ)
    (H J : Vec d → Vec d → Vec d)
    (hH : Measurable (Function.uncurry H)) (hJ : Measurable (Function.uncurry J))
    (g : Vec d → Vec d) (hg : IntegrableOn g (reflectionBox m) volume)
    {M N : ℝ} (hM : ∀ x y, ‖H x y‖ ≤ M) (hN : ∀ x y, ‖J x y‖ ≤ N) (x : Vec d) :
    periodicKernelOperator m H g x - periodicKernelOperator m J g x =
      periodicKernelOperator m (fun x y => H x y - J x y) g x := by
  rw [periodicKernelOperator, periodicKernelOperator,
    ← integral_sub (integrable_periodicKernelOperator_integrand m H hH g hg hM x)
      (integrable_periodicKernelOperator_integrand m J hJ g hg hN x)]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

end

end CoarseDeGiorgi.Foundations.Reconstruction
