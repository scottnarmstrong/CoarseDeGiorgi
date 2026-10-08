module

public import CoarseDeGiorgi.Endpoint.Morrey.Kernel

/-! # Smooth Morrey estimate on bounded convex domains

The pointwise Riesz representation and Hölder give a uniform oscillation bound.
This module keeps the domain and diameter explicit; scaling to cubes and passage
to weak representatives are separate steps.
-/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Morrey

open Homogenization MeasureTheory
open scoped ENNReal

theorem integral_mul_norm_le_eLpNorm_toReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} {p s : ℝ} (hps : p.HolderConjugate s)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal s) μ) :
    ∫ x, ‖f x‖ * ‖g x‖ ∂μ ≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal *
        (eLpNorm g (ENNReal.ofReal s) μ).toReal := by
  have heq {h : α → ℝ} {r : ℝ} (hr : 0 < r) (hh : MemLp h (ENNReal.ofReal r) μ) :
      (eLpNorm h (ENNReal.ofReal r) μ).toReal =
        (∫ x, ‖h x‖ ^ r ∂μ) ^ (1 / r) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hr).ne'
      ENNReal.ofReal_ne_top hh, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal (Real.rpow_nonneg
        (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _), one_div]
  rw [heq hps.pos hf, heq hps.symm.pos hg]
  exact integral_mul_norm_le_Lp_mul_Lq hps hf hg

/-- A smooth function's oscillation about its average has a uniform bound if
the Riesz kernel is in the dual gradient space. -/
theorem exists_smooth_morrey_bound {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {p s : ℝ} (hps : p.HolderConjugate s) (hds : ((d : ℝ) - 1) * s < d)
    (R : ℝ) (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖y - x‖ < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u →
      MemLp (fun x => ‖fderiv ℝ u x‖) (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm (fun x => u x - integralAverage U u) ⊤ (volume.restrict U) ≤
        ENNReal.ofReal C *
          eLpNorm (fun x => ‖fderiv ℝ u x‖) (ENNReal.ofReal p) (volume.restrict U) := by
  let : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  let B : ℝ := (volume U).toReal⁻¹ *
    (((2 * Classical.choose hU.isBoundedDomain) ^ d) / (d : ℝ))
  let K := eLpNorm (fun y : Vec d => rieszKernel 0 y) (ENNReal.ofReal s)
    (volume.restrict (Metric.ball 0 R))
  let C : ℝ := B * K.toReal
  have hradius : 0 < Classical.choose hU.isBoundedDomain :=
    (Classical.choose_spec hU.isBoundedDomain).1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hKtop : K ≠ ⊤ := (riesz_kernel_memLp_ball hps.symm.pos hds R).eLpNorm_ne_top
  refine ⟨C, mul_nonneg hB ENNReal.toReal_nonneg, ?_⟩
  intro u hu hgrad
  have hvol : 0 < (volume U).toReal := ENNReal.toReal_pos
    (hU.isOpen.measure_pos volume hne).ne' hU.isBoundedDomain.isBounded.measure_lt_top.ne
  have huInt : IntegrableOn u U :=
    (hu.continuous.continuousOn.integrableOn_compact
      hU.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  have hpoint : ∀ x ∈ U, ‖u x - integralAverage U u‖ ≤
      C * (eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
        (volume.restrict U)).toReal := by
    intro x hx
    have hkBound := eLpNorm_riesz_kernel_le_ball hps.symm.pos hds R U x (hdiam x hx)
    have hkLp : MemLp (rieszKernel x) (ENNReal.ofReal s) (volume.restrict U) :=
      hkBound.trans_lt (lt_top_iff_ne_top.mpr hKtop)
    have hHolder := integral_mul_norm_le_eLpNorm_toReal hps hgrad hkLp
    simp only [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (rieszKernel_nonneg _ _)] at hHolder
    have hrepr :=
      norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_rieszKernel_of_isOpenBoundedConvexDomain
        hU huInt hu hx hvol
    calc
      ‖u x - integralAverage U u‖ ≤
          B * ∫ y in U, ‖fderiv ℝ u y‖ * rieszKernel x y := by
            simpa only [B, mul_assoc] using hrepr
      _ ≤ B * ((eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
          (volume.restrict U)).toReal *
            (eLpNorm (rieszKernel x) (ENNReal.ofReal s) (volume.restrict U)).toReal) :=
        mul_le_mul_of_nonneg_left hHolder hB
      _ ≤ B * ((eLpNorm (fun y => ‖fderiv ℝ u y‖) (ENNReal.ofReal p)
          (volume.restrict U)).toReal * K.toReal) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hKtop hkBound)
            ENNReal.toReal_nonneg) hB
      _ = _ := by dsimp [C]; ring
  have hsup := eLpNormEssSup_le_of_ae_bound (μ := volume.restrict U)
    ((ae_restrict_mem hU.isOpen.measurableSet).mono fun x hx => hpoint x hx)
  have hm : AEStronglyMeasurable (fun x => u x - integralAverage U u)
      (volume.restrict U) := (hu.continuous.sub continuous_const).aestronglyMeasurable
  rw [eLpNorm_exponent_top hm]
  refine hsup.trans_eq ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hB ENNReal.toReal_nonneg),
    ENNReal.ofReal_toReal hgrad.eLpNorm_ne_top]

end CoarseDeGiorgi.Endpoint.Morrey
