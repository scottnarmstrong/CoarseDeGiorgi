module

public import CoarseDeGiorgi.Endpoint.Morrey.Approximation
public import Homogenization.Sobolev.Foundations.PoincareW1p.Dilation
public import Homogenization.Sobolev.Foundations.PoincareW1p.Translation
public import Homogenization.Geometry.TriadicCubeTranslation

/-! # Translation and dilation of the weak Morrey estimate -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Morrey

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Pointwise

noncomputable section

variable {d : ℕ} {U V : Set (Vec d)} {p : ℝ≥0∞}

def castW1pDomain (hUV : U = V) (u : W1pFunction U p) : W1pFunction V p := hUV ▸ u

@[simp] theorem castW1pDomain_toFun (hUV : U = V) (u : W1pFunction U p) :
    (castW1pDomain hUV u).toFun = u.toFun := by subst V; rfl

@[simp] theorem castW1pDomain_grad (hUV : U = V) (u : W1pFunction U p) :
    (castW1pDomain hUV u).grad = u.grad := by subst V; rfl

def untranslateW1p (z : Vec d) (u : W1pFunction (translateSet z U) p) :
    W1pFunction U p :=
  castW1pDomain (by rw [translateSet_translateSet]; simp) (u.translate (-z))

@[simp] theorem untranslateW1p_toFun (z : Vec d)
    (u : W1pFunction (translateSet z U) p) (x : Vec d) :
    (untranslateW1p z u).toFun x = u.toFun (x + z) := by
  simp [untranslateW1p, W1pFunction.translate, sub_eq_add_neg]

@[simp] theorem untranslateW1p_grad (z : Vec d)
    (u : W1pFunction (translateSet z U) p) (x : Vec d) :
    (untranslateW1p z u).grad x = u.grad (x + z) := by
  simp [untranslateW1p, W1pFunction.translate, sub_eq_add_neg]

theorem integralAverage_untranslateW1p (z : Vec d)
    (u : W1pFunction (translateSet z U) p) :
    integralAverage U (untranslateW1p z u).toFun =
      integralAverage (translateSet z U) u.toFun := by
  unfold integralAverage
  rw [volume_translateSet_eq]
  simp only [untranslateW1p_toFun]
  rw [setIntegral_comp_addRight_translateSet]

theorem gradientCoordLpSeminormSum_untranslateW1p (z : Vec d)
    (u : W1pFunction (translateSet z U) p) :
    (untranslateW1p z u).gradientCoordLpSeminormSum = u.gradientCoordLpSeminormSum := by
  unfold W1pFunction.gradientCoordLpSeminormSum W1pFunction.gradCoordLpSeminorm
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg ENNReal.toReal
  simpa only [untranslateW1p_grad, Function.comp_def, volumeMeasureOn] using
    eLpNorm_comp_measurePreserving (u.gradMemLp i).aestronglyMeasurable
      (measurePreserving_addRight_restrict_translateSet z U)

theorem eLpNorm_subAverage_untranslateW1p (z : Vec d)
    (u : W1pFunction (translateSet z U) p) (q : ℝ≥0∞) :
    eLpNorm (fun x => (untranslateW1p z u).toFun x -
        integralAverage U (untranslateW1p z u).toFun) q (volume.restrict U) =
      eLpNorm (fun x => u.toFun x - integralAverage (translateSet z U) u.toFun) q
        (volume.restrict (translateSet z U)) := by
  rw [integralAverage_untranslateW1p]
  simpa only [untranslateW1p_toFun, Function.comp_def, Pi.sub_apply] using
    eLpNorm_comp_measurePreserving
      (g := fun x => u.toFun x - integralAverage (translateSet z U) u.toFun)
      (u.memLp.aestronglyMeasurable.sub aestronglyMeasurable_const)
      (measurePreserving_addRight_restrict_translateSet z U)

/-- Dilation preserves the essential supremum on the corresponding domain. -/
theorem eLpNorm_top_comp_smul {a : ℝ} (ha : 0 < a) {E : Type*}
    [NormedAddCommGroup E] {f : Vec d → E}
    (hf : AEStronglyMeasurable f (volume.restrict (a • U))) :
    eLpNorm (fun x => f (a • x)) ⊤ (volume.restrict U) =
      eLpNorm f ⊤ (volume.restrict (a • U)) := by
  have hmap := map_smul_volume_restrict (d := d) ha U
  have hm : AEStronglyMeasurable f
      (Measure.map (fun x : Vec d => a • x) (volume.restrict U)) := by
    rw [hmap]
    exact hf.mono_ac Measure.smul_absolutelyContinuous
  change eLpNorm (f ∘ fun x => a • x) ⊤ (volume.restrict U) = _
  rw [← eLpNorm_map_measure hm (measurable_const_smul a).aemeasurable,
    hmap, eLpNorm_smul_measure_of_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne']
  simp

theorem eLpNorm_top_subAverage_unscale {a : ℝ} (ha : 0 < a)
    (u : W1pFunction (a • U) p) :
    eLpNorm (fun x => (u.unscale ha).toFun x - integralAverage U (u.unscale ha).toFun)
        ⊤ (volume.restrict U) =
      eLpNorm (fun x => u.toFun x - integralAverage (a • U) u.toFun)
        ⊤ (volume.restrict (a • U)) := by
  rw [W1pFunction.integralAverage_unscale_eq]
  exact eLpNorm_top_comp_smul ha (u.memLp.aestronglyMeasurable.sub aestronglyMeasurable_const)

theorem exists_cube_weak_morrey_bound {d : ℕ} [NeZero d] {p s : ℝ}
    (hps : p.HolderConjugate s) (hds : ((d : ℝ) - 1) * s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : TriadicCube d)
      (u : W1pFunction (openCubeSet Q) (ENNReal.ofReal p)),
      eLpNorm (fun x => u.toFun x - integralAverage (openCubeSet Q) u.toFun)
        ⊤ (volume.restrict (openCubeSet Q)) ≤
      ENNReal.ofReal (C * cubeScaleFactor Q *
        W1pFunction.dilationLpFactor d (ENNReal.ofReal p) (cubeScaleFactor Q)⁻¹ *
        u.gradientCoordLpSeminormSum) := by
  let U0 := openCubeSet (Homogenization.originCube d 0)
  have hU : IsOpenBoundedConvexDomain U0 := isOpenBoundedConvexDomain_openCubeSet _
  have hne : U0.Nonempty := by
    refine ⟨0, ?_⟩
    intro i
    simp [Homogenization.originCube, cubeScaleFactor]
  have hdiam : ∀ x ∈ U0, ∀ y ∈ U0, ‖y - x‖ < 1 := by
    intro x hx y hy
    rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
    intro i
    have hxi := hx i
    have hyi := hy i
    simp only [Homogenization.originCube, cubeScaleFactor,
      zpow_zero, Int.cast_zero, Pi.zero_apply] at hxi hyi
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]
  obtain ⟨C, hC, hbase⟩ := exists_weak_morrey_bound hU hne hps hds 1 hdiam
  refine ⟨C, hC, ?_⟩
  intro Q
  rw [openCubeSet_eq_translateSet_smul_originCube_zero Q]
  intro u
  let a := cubeScaleFactor Q
  have ha : 0 < a := zpow_pos (by norm_num) _
  let uD : W1pFunction (a • U0) (ENNReal.ofReal p) := untranslateW1p (triadicCubeShift Q) u
  let u0 : W1pFunction U0 (ENNReal.ofReal p) := uD.unscale ha
  have hb := hbase u0
  have hnorm := (eLpNorm_top_subAverage_unscale ha uD).trans
    (eLpNorm_subAverage_untranslateW1p (triadicCubeShift Q) u ⊤)
  rw [hnorm] at hb
  rw [W1pFunction.gradientCoordLpSeminormSum_unscale_eq ha ENNReal.ofReal_ne_top,
    gradientCoordLpSeminormSum_untranslateW1p] at hb
  convert hb using 1
  congr 1
  ring

end

end CoarseDeGiorgi.Endpoint.Morrey
