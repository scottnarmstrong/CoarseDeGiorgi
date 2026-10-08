module

public import Homogenization.Sobolev.Foundations.PoincareLp
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Integrability of the Morrey kernel

The Riesz kernel lies in the Hölder dual space when the gradient exponent
exceeds the dimension. The criterion is expressed directly in terms of the
kernel exponent, so it can also be reused with other finite Hölder pairs.
-/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Morrey

open Homogenization MeasureTheory
open scoped ENNReal

theorem riesz_kernel_memLp_ball {d : ℕ} [NeZero d] {s : ℝ}
    (hs : 0 < s) (hds : ((d : ℝ) - 1) * s < d) (R : ℝ) :
    MemLp (fun x : Vec d => rieszKernel 0 x) (ENNReal.ofReal s)
      (volume.restrict (Metric.ball 0 R)) := by
  have hm : Measurable (fun x : Vec d => rieszKernel 0 x) := by
    unfold rieszKernel
    exact (measurable_const.sub measurable_id).norm.pow_const _
  have hmeas := hm.aestronglyMeasurable (μ := volume)
  have hdim : 1 ≤ Module.finrank ℝ (Vec d) := by
    simpa only [Vec, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
      Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hexp : ((d : ℝ) - 1) * s < (Module.finrank ℝ (Vec d) : ℝ) := by
    simpa only [Vec, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hds
  have hint : IntegrableOn (fun x : Vec d => ‖rieszKernel 0 x‖ ^ s) (Metric.ball 0 R) := by
    apply integrableOn_ball_of_norm_le_rpow hdim hexp (C := 1)
    · filter_upwards with x
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        Real.norm_of_nonneg (rieszKernel_nonneg _ _)]
      simp only [rieszKernel, zero_sub, norm_neg, ← Real.rpow_mul (norm_nonneg _), one_mul]
      exact le_of_eq (congrArg (Real.rpow ‖x‖) (by ring))
    · exact (hm.norm.pow_const s).aestronglyMeasurable
  exact (integrable_norm_rpow_iff (p := ENNReal.ofReal s) hmeas.restrict
    (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top).mp
    (by simpa only [IntegrableOn, ENNReal.toReal_ofReal hs.le] using hint)

/-- Translation gives a uniform kernel norm on every set contained in a ball
about the evaluation point. -/
theorem eLpNorm_riesz_kernel_le_ball {d : ℕ} [NeZero d] {s : ℝ}
    (hs : 0 < s) (hds : ((d : ℝ) - 1) * s < d) (R : ℝ)
    (U : Set (Vec d)) (x : Vec d) (hU : ∀ y ∈ U, ‖y - x‖ < R) :
    eLpNorm (rieszKernel x) (ENNReal.ofReal s) (volume.restrict U) ≤
      eLpNorm (fun y : Vec d => rieszKernel 0 y) (ENNReal.ofReal s)
        (volume.restrict (Metric.ball 0 R)) := by
  have hsub : U ⊆ translateSet x (Metric.ball 0 R) := by
    intro y hy
    apply mem_translateSet_iff_sub_mem.mpr
    simpa only [Metric.mem_ball, dist_zero_right] using hU y hy
  have hmono : eLpNorm (rieszKernel x) (ENNReal.ofReal s) (volume.restrict U) ≤
      eLpNorm (rieszKernel x) (ENNReal.ofReal s)
        (volume.restrict (translateSet x (Metric.ball 0 R))) :=
    eLpNorm_mono_measure (rieszKernel x) (Measure.restrict_mono hsub le_rfl)
  refine hmono.trans_eq ?_
  have hbase := riesz_kernel_memLp_ball hs hds R
  have h := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal s)
    hbase.aestronglyMeasurable
    (measurePreserving_subRight_restrict_translateSet x (Metric.ball 0 R))
  convert h using 1
  congr 1
  funext y
  simp only [Function.comp_apply, rieszKernel, zero_sub, norm_neg, norm_sub_rev]

end CoarseDeGiorgi.Endpoint.Morrey
