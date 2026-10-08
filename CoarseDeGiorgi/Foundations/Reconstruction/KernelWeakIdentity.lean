module

public import CoarseDeGiorgi.Foundations.Reconstruction.LowestKernel
public import CoarseDeGiorgi.Foundations.Reconstruction.ReflectedAverages

/-! # Reconstructing scalar blocks from the reflected weak gradient -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- A periodic vector kernel can be used as a translated scalar weak test, coordinate by coordinate. -/
theorem kernel_weak_identity_coordinate {m : ℤ} {z : Fin d → ℤ}
    {w : Vec d → ℝ} {Dw : Vec d → Vec d}
    (hweak : HasWeakGradientOn (auxCube m z) w Dw)
    (hw : IntegrableOn w (auxCube m z) volume)
    (hDw : IntegrableOn Dw (auxCube m z) volume)
    (K : Vec d → Vec d) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hperiod : ∀ i x, K (x + (2 * auxSide m) • basisVec i) = K x)
    (x : Vec d) (i : Fin d) :
    ∫ y in reflectionBox m, reflectedScalar m z w y *
      (fderiv ℝ K (x - y) (basisVec i)) i ∂volume =
      ∫ y in reflectionBox m, reflectedPartial m z Dw i y * K (x - y) i ∂volume := by
  let φ := fun y => K (x - y) i
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).contDiff.comp
      (hK.comp (contDiff_const.sub contDiff_id))
  have hp (y : Vec d) : φ (y + (2 * auxSide m) • basisVec i) = φ y := by
    have h := hperiod i (x - y - (2 * auxSide m) • basisVec i)
    rw [show x - y - (2 * auxSide m) • basisVec i +
      (2 * auxSide m) • basisVec i = x - y by abel] at h
    change K (x - (y + (2 * auxSide m) • basisVec i)) i = K (x - y) i
    rw [show x - (y + (2 * auxSide m) • basisVec i) =
      x - y - (2 * auxSide m) • basisVec i by abel, h]
  have hD (y : Vec d) : (fderiv ℝ φ y) (basisVec i) =
      -(fderiv ℝ K (x - y) (basisVec i)) i := by
    have hd := (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).hasFDerivAt.comp y
      (((hK.differentiable (by norm_num)) (x - y)).hasFDerivAt.comp y
        ((hasFDerivAt_const x y).sub (hasFDerivAt_id y)))
    change HasFDerivAt φ _ y at hd
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      zero_sub, neg_apply, ContinuousLinearMap.id_apply, map_neg]
  have h := reflected_integration_by_parts hweak hw hDw i hφ hp
  apply neg_inj.mp
  simpa only [hD, mul_neg, integral_neg] using h

/-- A finite-box bound makes each smooth-kernel pairing integrable. -/
theorem integrableOn_reflectionBox_mul_continuous {m : ℤ} {f g : Vec d → ℝ}
    (hf : IntegrableOn f (reflectionBox m) volume) (hg : Continuous g) :
    IntegrableOn (fun x => f x * g x) (reflectionBox m) volume := by
  have hm : MeasurableSet (reflectionBox (d := d) m) := by
    have hopen : IsOpen (reflectionBox (d := d) m) := by
      simp only [reflectionBox, ← Set.iInter_ofPred]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).abs continuous_const
    exact hopen.measurableSet
  apply integrableOn_mul_continuous_ball hf hg hm
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (auxSide_pos m).le).mpr fun i =>
    (by simpa only [Real.norm_eq_abs] using (hx i).le)

/-- The kernel divergence pairing equals its vector pairing with the weak gradient. -/
theorem kernel_weak_identity {m : ℤ} {z : Fin d → ℤ}
    {w : Vec d → ℝ} {Dw : Vec d → Vec d}
    (hweak : HasWeakGradientOn (auxCube m z) w Dw)
    (hw : IntegrableOn w (auxCube m z) volume)
    (hDw : IntegrableOn Dw (auxCube m z) volume)
    (K : Vec d → Vec d) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hperiod : ∀ i x, K (x + (2 * auxSide m) • basisVec i) = K x) (x : Vec d) :
    ∫ y in reflectionBox m, reflectedScalar m z w y * vectorDivergence K (x - y) ∂volume =
      ∫ y in reflectionBox m, vecDot (K (x - y)) (reflectedGradient m z Dw y) ∂volume := by
  have hleft (i : Fin d) : IntegrableOn
      (fun y => reflectedScalar m z w y * (fderiv ℝ K (x - y) (basisVec i)) i)
        (reflectionBox m) volume := by
    apply integrableOn_reflectionBox_mul_continuous (integrableOn_reflectedScalar hw)
    exact (continuous_apply i).comp
      (((hK.continuous_fderiv (by norm_num)).comp (continuous_const.sub continuous_id)).clm_apply
        continuous_const)
  have hright (i : Fin d) : IntegrableOn
      (fun y => reflectedPartial m z Dw i y * K (x - y) i) (reflectionBox m) volume :=
    integrableOn_reflectionBox_mul_continuous (integrableOn_reflectedPartial hDw i)
      ((continuous_apply i).comp (hK.continuous.comp (continuous_const.sub continuous_id)))
  simp only [vectorDivergence, Finset.mul_sum, vecDot, reflectedGradient]
  rw [integral_finsetSum _ (fun i _ => hleft i), integral_finsetSum _ (fun i _ => ?_)]
  · apply Finset.sum_congr rfl
    intro i _
    rw [kernel_weak_identity_coordinate hweak hw hDw K hK hperiod x i]
    apply integral_congr_ae
    exact ae_of_all _ fun y => mul_comm _ _
  · apply (hright i).congr
    exact ae_of_all _ fun y => mul_comm _ _

end

end CoarseDeGiorgi.Foundations.Reconstruction
