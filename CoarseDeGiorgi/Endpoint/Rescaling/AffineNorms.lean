module

public import CoarseDeGiorgi.Endpoint.Rescaling.AffineMeasure
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.NormalizedLpMoment

/-! Transport of finite norms and essential values, including nonmeasurable functions. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Endpoint.Rescaling

theorem eLpNorm_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (u : Vec d → ℝ) (p : ℝ≥0∞) :
    eLpNorm (u ∘ affineMap y r) p (volume.restrict U) =
      (ENNReal.ofReal ((r ^ d)⁻¹)).rpow (1 / p.toReal) *
        eLpNorm u p (volume.restrict (affineImage y r U)) := by
  rw [← (affineMap_measurableEmbedding y hr).eLpNorm_map_measure,
    map_affineMap_restrict y hr U]
  have hj : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, smul_eq_mul, ENNReal.rpow_eq_pow] using
    eLpNorm_smul_measure_of_ne_zero hj u p (volume.restrict (affineImage y r U))

theorem eLpNorm_top_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (u : Vec d → ℝ) :
    eLpNorm (u ∘ affineMap y r) ⊤ (volume.restrict U) =
      eLpNorm u ⊤ (volume.restrict (affineImage y r U)) := by
  rw [eLpNorm_affine y hr U u]
  simp

theorem nonnegativeEssInf_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (u : Vec d → ℝ) :
    nonnegativeEssInf U (u ∘ affineMap y r) =
      nonnegativeEssInf (affineImage y r U) u := by
  unfold nonnegativeEssInf
  have h := (affineMap_measurableEmbedding y hr).essSup_map_measure (β := ℝ≥0∞ᵒᵈ)
    (g := fun x => (ENNReal.ofReal (u x) : ℝ≥0∞ᵒᵈ)) (μ := volume.restrict U)
  change essInf (fun x => ENNReal.ofReal (u x))
    (Measure.map (affineMap y r) (volume.restrict U)) =
    essInf (fun x => ENNReal.ofReal ((u ∘ affineMap y r) x)) (volume.restrict U) at h
  rw [map_affineMap_restrict y hr U] at h
  unfold essInf at h ⊢
  rw [Measure.ae_ennreal_smul_measure_eq
    ((ne_of_gt ∘ ENNReal.ofReal_pos.mpr) (by positivity : 0 < (r ^ d)⁻¹))] at h
  exact h.symm

theorem normalizedLpMoment_affine {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r)
    (U : Set (Vec d)) (u : Vec d → ℝ) {p : ℝ} (hp : 0 < p) :
    normalizedLpMoment p hp U (u ∘ affineMap y r) =
      normalizedLpMoment p hp (affineImage y r U) u := by
  unfold normalizedLpMoment
  simp only [Function.comp_apply]
  rw [volume_affine y hr U,
    lintegral_affine y hr U (fun x => (ENNReal.ofReal |u x|).rpow p),
    ENNReal.mul_inv (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))))
      (Or.inl ENNReal.ofReal_ne_top)]
  have hj0 : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 :=
    (ne_of_gt ∘ ENNReal.ofReal_pos.mpr) (by positivity)
  congr 1
  calc
    _ = (ENNReal.ofReal ((r ^ d)⁻¹))⁻¹ * ENNReal.ofReal ((r ^ d)⁻¹) *
        ((volume (affineImage y r U))⁻¹ *
          ∫⁻ x in affineImage y r U, (ENNReal.ofReal |u x|).rpow p) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hj0 ENNReal.ofReal_ne_top, one_mul]

end CoarseDeGiorgi.Endpoint.Rescaling
