import CoarseDeGiorgi.Weighted.Identification

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The positive quadratic form is bounded above by trace times Euclidean norm squared. -/
theorem quadratic_le_trace_mul_length_sq (A : Mat d) (hA : A.PosDef) (z : Vec d) :
    vecDot z (matVecMul A z) ≤ A.trace * vecDot z z := by
  have hq : 0 ≤ vecDot z (matVecMul A z) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      hA.posSemidef.dotProduct_mulVec_nonneg (x := z)
  rcases eq_or_lt_of_le hq with hz | hz
  · rw [← hz]
    exact mul_nonneg hA.posSemidef.trace_nonneg (vecNormSq_nonneg z)
  · have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq z (matVecMul A z)
    have hflux := Foundations.vecDot_matVecMul_self_le_trace_mul_quadratic A hA z
    have hmul : vecDot z (matVecMul A z) * vecDot z (matVecMul A z) ≤
        (A.trace * vecDot z z) * vecDot z (matVecMul A z) := by
      calc
        _ ≤ vecDot z z * vecDot (matVecMul A z) (matVecMul A z) := by simpa only [vecNormSq, pow_two] using hcs
        _ ≤ vecDot z z * (A.trace * vecDot z (matVecMul A z)) :=
          mul_le_mul_of_nonneg_left hflux (vecNormSq_nonneg z)
        _ = (A.trace * vecDot z z) * vecDot z (matVecMul A z) := by ring
    exact le_of_mul_le_mul_right hmul hz

/-- Globally smooth compactly supported tests have finite energy under the coefficient hypotheses. -/
theorem isSmoothCore_of_supported (ha : IsWeightedCoeffOn V a)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    IsSmoothCore a V f := by
  have hGcont : Continuous (smoothGrad f) := by
    apply continuous_pi
    intro i
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hGsupport : HasCompactSupport (smoothGrad f) := by
    apply HasCompactSupport.mono' (hc.fderiv ℝ)
    intro x hx
    apply subset_tsupport
    rw [Function.mem_support]
    intro hz
    apply hx
    funext i
    simp only [smoothGrad, CoarseDeGiorgi.smoothGrad, hz, zero_apply, Pi.zero_apply]
  have hLcont : Continuous (fun x => vecDot (smoothGrad f x) (smoothGrad f x)) := by
    unfold vecDot
    fun_prop
  have hLsupport : HasCompactSupport (fun x => vecDot (smoothGrad f x) (smoothGrad f x)) := by
    apply HasCompactSupport.mono' hGsupport
    intro x hx
    apply subset_tsupport
    rw [Function.mem_support]
    intro hz
    apply hx
    change vecDot (smoothGrad f x) (smoothGrad f x) = 0
    rw [hz, vecDot_zero_left]
  obtain ⟨C, hC⟩ := hLsupport.exists_bound_of_continuous hLcont
  have hGM : AEStronglyMeasurable (smoothGrad f) (volume.restrict V) :=
    hGcont.aestronglyMeasurable
  have hqi : IntegrableOn (fun x => vecDot (smoothGrad f x) (matVecMul (a x) (smoothGrad f x))) V := by
    refine (ha.2.2.1.mul_const C).mono' (quadratic_aestronglyMeasurable ha hGM) ?_
    filter_upwards [ha.2.1, quadratic_nonneg ha (smoothGrad f)] with x hx hq
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    calc
      _ ≤ (a x).trace * vecDot (smoothGrad f x) (smoothGrad f x) :=
        quadratic_le_trace_mul_length_sq (a x) hx (smoothGrad f x)
      _ ≤ (a x).trace * C := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC x)) hx.posSemidef.trace_nonneg
  refine ⟨hf.contDiffOn, (hf.continuous.integrable_of_hasCompactSupport hc).integrableOn, ?_⟩
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
    (quadratic_aestronglyMeasurable ha hGM) (quadratic_nonneg ha (smoothGrad f))).mpr hqi)

/-- The approved zero-boundary completion is a subspace of the approved weighted completion. -/
theorem MemH1a0.memH1a (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a0 a V u G) : MemH1a a V u G := by
  obtain ⟨huM, hGM, f, hf, hc, hl, ht⟩ := hu
  exact ⟨huM, hGM, f, (fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1), hc, hl, ht⟩

/-- A supported smooth test has zero integral of each classical partial derivative. -/
theorem integral_smoothGrad_eq_zero {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ V)
    (i : Fin d) : (∫ x in V, smoothGrad f x i) = 0 := by
  have hdcont : Continuous (fun x => fderiv ℝ f x (basisVec i)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdi : Integrable (fun x => fderiv ℝ f x (basisVec i)) volume := hdcont.integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : Vec d => (1 : ℝ)) (g := f) (v := basisVec i)
    (by simp)
    (by simpa using hdi) (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _) (fun _ _ => (hf.differentiable (by simp)).differentiableAt)
  have hz : (∫ x, fderiv ℝ f x (basisVec i)) = 0 := by simpa using hibp
  change (∫ x in V, fderiv ℝ f x (basisVec i)) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hz
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ f y (basisVec i))
    intro h
    exact hx (hs (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := f) (basisVec i) h))

end CoarseDeGiorgi.Weighted
