import CoarseDeGiorgi.Weighted.HarmonicProperties
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The affine datum associated with a direction. -/
noncomputable def responseAffine (e : Vec d) : Vec d →L[ℝ] ℝ :=
  (show Vec d →ₗ[ℝ] ℝ from
    { toFun := vecDot e
      map_add' := vecDot_add_right e
      map_smul' := fun c x => vecDot_smul_right e x c }).toContinuousLinearMap

@[simp] theorem smoothGrad_responseAffine (e : Vec d) :
    smoothGrad (responseAffine e) = fun _ => e := by
  funext x i
  have h_eval (y : Vec d) : responseAffine e y = vecDot e y := rfl
  simp [smoothGrad, CoarseDeGiorgi.smoothGrad, ContinuousLinearMap.fderiv,
    h_eval, vecDot_basisVec_right]

/-- Constant vector fields have finite energy under the trace assumption. -/
noncomputable def constantEnergyField (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    GradientCore ha := by
  refine ⟨fun _ => e, aestronglyMeasurable_const, ?_⟩
  apply (ha.2.2.1.mul_const (vecDot e e)).mono'
    (quadratic_aestronglyMeasurable ha aestronglyMeasurable_const)
  filter_upwards [ha.2.1] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      hx.posSemidef.dotProduct_mulVec_nonneg (x := e))]
  exact quadratic_le_trace_mul_length_sq (a x) hx e


/-- Affine functions belong to the literal smooth core. -/
theorem responseAffine_isSmoothCore (hV : IsOpenBoundedConvexDomain V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) : IsSmoothCore a V (responseAffine e) := by
  refine ⟨(responseAffine e).contDiff.contDiffOn, ?_, ?_⟩
  · exact ((responseAffine e).continuous.continuousOn.integrableOn_compact
      hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  · change weightedEnergy a V (smoothGrad (responseAffine e)) < ⊤
    rw [smoothGrad_responseAffine]
    exact GradientCore.energy_lt_top ha (constantEnergyField ha e)

/-- A smooth core element is represented by its constant approximation sequence. -/
theorem memH1a_of_isSmoothCore (hV : IsOpen V) (_ha : IsWeightedCoeffOn V a)
    {f : Vec d → ℝ} (hf : IsSmoothCore a V f) : MemH1a a V f (smoothGrad f) := by
  refine ⟨hf.2.1.aestronglyMeasurable, smoothGrad_aestronglyMeasurable hV hf.1,
    fun _ => f, fun _ => hf, ?_, ?_, ?_⟩
  · intro ε hε
    refine ⟨0, fun m n _ _ => ?_⟩
    simpa [weightedEnergy, CoarseDeGiorgi.weightedEnergy, volumeAverage, vecDot,
      matVecMul] using (ENNReal.ofReal_pos.mpr hε)
  · intro K _ _
    simpa only [sub_self, enorm_zero, lintegral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (nhds 0))
  · simp [CoarseDeGiorgi.weightedEnergy, vecDot, matVecMul]

theorem responseAffine_memH1a (hV : IsOpenBoundedConvexDomain V)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    MemH1a a V (responseAffine e) (fun _ => e) := by
  simpa only [smoothGrad_responseAffine] using
    memH1a_of_isSmoothCore hV.isOpen ha (responseAffine_isSmoothCore hV ha e)

/-- The constant-field map before passage to the Hilbert completion. -/
noncomputable def constantEnergyLinear (ha : IsWeightedCoeffOn V a) :
    Vec d →ₗ[ℝ] GradientCore ha where
  toFun := constantEnergyField ha
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

end CoarseDeGiorgi.Weighted
