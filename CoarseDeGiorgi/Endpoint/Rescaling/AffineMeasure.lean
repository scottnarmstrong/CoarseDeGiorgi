module

public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import Homogenization.Geometry.Translation
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Sobolev.Foundations.CoerciveH1Dilation

/-! Measure transport for the affine maps used in the interior estimates. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace CoarseDeGiorgi.Endpoint.Rescaling

/-- Dilation by `r`, followed by translation by `y`. -/
def affineMap {d : ℕ} (y : Vec d) (r : ℝ) (x : Vec d) : Vec d :=
  r • x + y

/-- The image of a set under the interior affine map. -/
def affineImage {d : ℕ} (y : Vec d) (r : ℝ) (U : Set (Vec d)) : Set (Vec d) :=
  translateSet y (r • U)

theorem affineMap_measurable {d : ℕ} (y : Vec d) (r : ℝ) :
    Measurable (affineMap y r) :=
  (measurable_const_smul r).add_const y

theorem map_affineMap_restrict {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) :
    Measure.map (affineMap y r) (volume.restrict U) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volume.restrict (affineImage y r U) := by
  change Measure.map ((fun x : Vec d => x + y) ∘ (fun x : Vec d => r • x)) _ = _
  rw [← Measure.map_map (measurable_add_const y) (measurable_const_smul r),
    map_smul_volume_restrict hr U,
    Measure.map_smul _ (measurable_add_const y).aemeasurable]
  rw [(measurePreserving_addRight_restrict_translateSet y (r • U)).map_eq]
  rfl

/-- The affine change of variables is a homeomorphism for a positive scale. -/
noncomputable def affineHomeomorph {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) : Vec d ≃ₜ Vec d :=
  (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight y)

theorem affineMap_measurableEmbedding {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (affineMap y r) :=
  (affineHomeomorph y hr).measurableEmbedding

theorem lintegral_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (f : Vec d → ℝ≥0∞) :
    ∫⁻ x in U, f (affineMap y r x) =
      ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ x in affineImage y r U, f x := by
  rw [← (affineMap_measurableEmbedding y hr).lintegral_map f,
    map_affineMap_restrict y hr U, lintegral_smul_measure]
  rfl

theorem integral_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (f : Vec d → ℝ) :
    ∫ x in U, f (affineMap y r x) =
      (r ^ d)⁻¹ * ∫ x in affineImage y r U, f x := by
  rw [← (affineMap_measurableEmbedding y hr).integral_map f,
    map_affineMap_restrict y hr U, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ d)⁻¹)]
  rfl

theorem volume_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) :
    volume U = ENNReal.ofReal ((r ^ d)⁻¹) * volume (affineImage y r U) := by
  simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using
    lintegral_affine y hr U (fun _ => 1)

theorem volumeAverage_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage U (f ∘ affineMap y r) = volumeAverage (affineImage y r U) f := by
  have hj : (r ^ d)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hr.ne')
  unfold volumeAverage
  simp only [Function.comp_def]
  rw [volume_affine y hr U, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ d)⁻¹), integral_affine y hr U f,
    mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc ((r ^ d)⁻¹)⁻¹ ((r ^ d)⁻¹), inv_mul_cancel₀ hj, one_mul]

theorem affineMap_image {d : ℕ} (y : Vec d) (r : ℝ) (U : Set (Vec d)) :
    affineMap y r '' U = affineImage y r U := by
  rw [affineImage, ← image_addRight_eq_translateSet, ← Set.image_smul,
    Set.image_image]
  rfl

theorem weightedCoeffOn_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsWeightedCoeffOn (affineImage y r U) a) :
    IsWeightedCoeffOn U (a ∘ affineMap y r) := by
  have hmap := map_affineMap_restrict y hr U
  have hmeas : AEMeasurable (affineMap y r) (volume.restrict U) :=
    (affineMap_measurable y r).aemeasurable
  have ha_map : AEStronglyMeasurable a
      (Measure.map (affineMap y r) (volume.restrict U)) := by
    rw [hmap]
    exact ha.1.smul_measure _
  refine ⟨ha_map.comp_aemeasurable hmeas, ?_, ?_, ?_⟩
  · have hpos : ∀ᵐ x ∂(Measure.map (affineMap y r) (volume.restrict U)),
        (a x).PosDef := by
      rw [hmap]
      exact Measure.ae_smul_measure ha.2.1 _
    exact (ae_of_ae_map hmeas hpos)
  · have htrace : Integrable (fun x => (a x).trace)
        (Measure.map (affineMap y r) (volume.restrict U)) := by
      rw [hmap]
      exact ha.2.2.1.smul_measure ENNReal.ofReal_ne_top
    exact htrace.comp_measurable (affineMap_measurable y r)
  · have htrace : Integrable (fun x => ((a x)⁻¹).trace)
        (Measure.map (affineMap y r) (volume.restrict U)) := by
      rw [hmap]
      exact ha.2.2.2.smul_measure ENNReal.ofReal_ne_top
    exact htrace.comp_measurable (affineMap_measurable y r)

end CoarseDeGiorgi.Endpoint.Rescaling
