import CoarseDeGiorgi.Endpoint.Rescaling.AffineMeasure
import CoarseDeGiorgi.Statements.IsSmoothCore
import CoarseDeGiorgi.Weighted.GradientHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Affine transport of gradients, weighted energy, and the smooth core. -/

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace CoarseDeGiorgi.Endpoint.Rescaling

theorem aestronglyMeasurable_affine {d : ℕ} {E : Type*} [TopologicalSpace E]
    (y : Vec d) {r : ℝ} (hr : 0 < r) {U : Set (Vec d)} {f : Vec d → E}
    (hf : AEStronglyMeasurable f (volume.restrict (affineImage y r U))) :
    AEStronglyMeasurable (f ∘ affineMap y r) (volume.restrict U) := by
  have hm : AEStronglyMeasurable f
      (Measure.map (affineMap y r) (volume.restrict U)) := by
    rw [map_affineMap_restrict y hr U]
    exact hf.smul_measure _
  exact hm.comp_measurable (affineMap_measurable y r)

theorem integrable_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : IntegrableOn f (affineImage y r U)) :
    IntegrableOn (f ∘ affineMap y r) U := by
  have hm : Integrable f (Measure.map (affineMap y r) (volume.restrict U)) := by
    rw [map_affineMap_restrict y hr U]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hm.comp_measurable (affineMap_measurable y r)

theorem weightedEnergy_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (a : CoeffField d) (G : Vec d → Vec d) :
    weightedEnergy (a ∘ affineMap y r) U (G ∘ affineMap y r) =
      ENNReal.ofReal ((r ^ d)⁻¹) * weightedEnergy a (affineImage y r U) G :=
  lintegral_affine y hr U (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))))

theorem weightedEnergy_const_smul {d : ℕ} (a : CoeffField d) (U : Set (Vec d))
    (G : Vec d → Vec d) (c : ℝ) :
    weightedEnergy a U (c • G) = ENNReal.ofReal (c ^ 2) * weightedEnergy a U G := by
  unfold weightedEnergy
  simp only [Pi.smul_apply, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  have h (x : Vec d) : c * (c * vecDot (G x) (matVecMul (a x) (G x))) =
      c ^ 2 * vecDot (G x) (matVecMul (a x) (G x)) := by ring
  simp_rw [h, ENNReal.ofReal_mul (sq_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem smoothGrad_affine {d : ℕ} (y : Vec d) (r : ℝ) {f : Vec d → ℝ}
    {x : Vec d} (hf : DifferentiableAt ℝ f (affineMap y r x)) :
    smoothGrad (f ∘ affineMap y r) x = r • smoothGrad f (affineMap y r x) := by
  ext i
  have hΦ : HasFDerivAt (affineMap y r)
      (r • ContinuousLinearMap.id ℝ (Vec d)) x := by
    exact ((hasFDerivAt_id x).const_smul r).add_const y
  rw [smoothGrad, fderiv_comp x hf hΦ.differentiableAt, hΦ.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

theorem affineImage_isOpen {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpen U) : IsOpen (affineImage y r U) := by
  rw [← affineMap_image]
  exact (affineHomeomorph y hr).isOpenMap U hU

theorem smoothGrad_affine_ae {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (affineImage y r U)) :
    smoothGrad (f ∘ affineMap y r) =ᵐ[volume.restrict U]
      r • (smoothGrad f ∘ affineMap y r) := by
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  have hx' : affineMap y r x ∈ affineImage y r U := by
    rw [← affineMap_image]
    exact Set.mem_image_of_mem _ hx
  exact smoothGrad_affine y r ((hf.differentiableOn (by simp) _ hx').differentiableAt
    ((affineImage_isOpen y hr hU).mem_nhds hx'))

theorem isSmoothCore_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} (hU : IsOpen U) {a : CoeffField d} {f : Vec d → ℝ}
    (hf : IsSmoothCore a (affineImage y r U) f) :
    IsSmoothCore (a ∘ affineMap y r) U (f ∘ affineMap y r) := by
  have hmaps : Set.MapsTo (affineMap y r) U (affineImage y r U) := by
    intro x hx
    rw [← affineMap_image]
    exact Set.mem_image_of_mem _ hx
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (affineMap y r) :=
    (contDiff_id.const_smul r).add contDiff_const
  refine ⟨hf.1.comp hΦ.contDiffOn hmaps, integrable_affine y hr hf.2.1, ?_⟩
  have he : weightedEnergy (a ∘ affineMap y r) U (smoothGrad (f ∘ affineMap y r)) =
      weightedEnergy (a ∘ affineMap y r) U (r • (smoothGrad f ∘ affineMap y r)) :=
    Weighted.energy_congr_ae (a := a ∘ affineMap y r) (smoothGrad_affine_ae y hr hU hf.1)
  rw [he, weightedEnergy_const_smul, weightedEnergy_affine y hr]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2.2)

theorem eLpNorm_one_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (affineImage y r U))) :
    eLpNorm (f ∘ affineMap y r) 1 (volume.restrict U) =
      ENNReal.ofReal ((r ^ d)⁻¹) * eLpNorm f 1 (volume.restrict (affineImage y r U)) := by
  rw [eLpNorm_one_eq_lintegral_enorm (aestronglyMeasurable_affine y hr hf),
    eLpNorm_one_eq_lintegral_enorm hf]
  exact lintegral_affine y hr U (fun x => ‖f x‖ₑ)

end CoarseDeGiorgi.Endpoint.Rescaling
