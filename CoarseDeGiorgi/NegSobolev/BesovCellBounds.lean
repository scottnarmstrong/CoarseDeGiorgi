module

public import CoarseDeGiorgi.NegSobolev.BesovPointwise
public import CoarseDeGiorgi.NegSobolev.GaussianCells

/-! # Gaussian bounds for a single positive matrix cell average -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- The norm of the integral is the cell volume times the norm of the average. -/
theorem norm_integral_eq_volume_mul_average {d : ℕ} (U : Set (Vec d)) (b : Vec d → Mat d)
    (hvol : 0 < (volume U).toReal) :
    ‖Matrix.of fun i j => ∫ y in U, b y i j‖ =
      (volume U).toReal * ‖volumeAverageMat U b‖ := by
  have heq : volumeAverageMat U b =
      (volume U).toReal⁻¹ • (Matrix.of fun i j => ∫ y in U, b y i j) := rfl
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvol.le),
    ← mul_assoc, mul_inv_cancel₀ hvol.ne', one_mul]

/-- A positive lower bound for the Gaussian on a cell bounds its matrix average
by the full Gaussian matrix integral. -/
theorem gaussianKernel_cell_lower {d : ℕ} (t : ℝ) (ht : 0 < t)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (b : Vec d → Mat d) (hb : ∀ i j, Integrable (fun y => b y i j) volume)
    (hpos : ∀ᵐ y ∂volume, (b y).PosSemidef) (x : Vec d)
    (hdiam : ∀ y ∈ U, vecNormSq (x - y) ≤ (d : ℝ) * t) :
    ((4 * Real.pi * t) ^ (-((d : ℝ) / 2)) * Real.exp (-((d : ℝ) / 4))) *
        (volume U).toReal * ‖volumeAverageMat U b‖ ≤
      ‖Matrix.of fun i j => ∫ y, gaussianKernel t ht (x - y) * b y i j‖ := by
  rw [mul_assoc, ← norm_integral_eq_volume_mul_average U b hvol]
  apply norm_integral_restrict_le_weighted U b hb hpos (fun y => gaussianKernel t ht (x - y))
    (fun i j => integrable_gaussianKernel_mul t ht x (hb i j))
    (Filter.Eventually.of_forall (fun y => gaussianKernel_nonneg t ht (x - y)))
    _ (by positivity)
  filter_upwards [ae_restrict_mem hU] with y hy
  exact gaussianKernel_lower_of_sq_le t ht (x - y) (hdiam y hy)

/-- Averaging the upper pointwise comparison over the cell provides a uniform
bound for the Gaussian weight on that cell. -/
theorem gaussianKernel_cell_weight_upper {d : ℕ} (t : ℝ) (ht : 0 < t)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (hfin : volume U ≠ ⊤) (x : Vec d)
    (hdiam : ∀ y ∈ U, ∀ z ∈ U, vecNormSq (y - z) ≤ (d : ℝ) * t)
    {y : Vec d} (hy : y ∈ U) :
    gaussianKernel t ht (x - y) ≤
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)) /
        (volume U).toReal * ∫ z in U, gaussianKernel (2 * t) (by positivity) (x - z) := by
  have : IsFiniteMeasure (volume.restrict U) := ⟨by simp only [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hi : Integrable (fun z => gaussianKernel (2 * t) (by positivity) (x - z)) volume :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (integrable_gaussianKernel (2 * t) (by positivity))
  have hle : ∫ _z in U, gaussianKernel t ht (x - y) ≤
      ∫ z in U, ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)) *
        gaussianKernel (2 * t) (by positivity) (x - z) := by
    apply integral_mono_ae (integrable_const _) (hi.restrict.const_mul _)
    filter_upwards [ae_restrict_mem hU] with z hz
    exact gaussianKernel_compare_of_sq_sub_le t ht x y z (hdiam y hy z hz)
  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, integral_const_mul] at hle
  simp only [measureReal_def] at hle
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hvol).mpr
  simpa only [mul_comm] using hle

/-- The matrix Gaussian integral over one cell is bounded by the Gaussian mass
of the cell at twice the time, multiplied by the norm of its average matrix. -/
theorem gaussianKernel_cell_upper {d : ℕ} (t : ℝ) (ht : 0 < t)
    (U : Set (Vec d)) (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (hfin : volume U ≠ ⊤) (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun y => b y i j) (volume.restrict U))
    (hpos : ∀ᵐ y ∂(volume.restrict U), (b y).PosSemidef) (x : Vec d)
    (hdiam : ∀ y ∈ U, ∀ z ∈ U, vecNormSq (y - z) ≤ (d : ℝ) * t) :
    ‖Matrix.of fun i j => ∫ y in U, gaussianKernel t ht (x - y) * b y i j‖ ≤
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)) *
        (∫ z in U, gaussianKernel (2 * t) (by positivity) (x - z)) *
          ‖volumeAverageMat U b‖ := by
  have hI : 0 ≤ ∫ z in U, gaussianKernel (2 * t) (by positivity) (x - z) :=
    integral_nonneg (fun z => gaussianKernel_nonneg _ _ _)
  have hle := norm_weighted_integral_le b hb hpos (fun y => gaussianKernel t ht (x - y))
    (((continuous_gaussianKernel t ht).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable.restrict)
    (((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)) / (volume U).toReal *
      ∫ z in U, gaussianKernel (2 * t) (by positivity) (x - z)) (by positivity)
    (Filter.Eventually.of_forall (fun y => gaussianKernel_nonneg t ht (x - y)))
    (by
      filter_upwards [ae_restrict_mem hU] with y hy
      exact gaussianKernel_cell_weight_upper t ht U hU hvol hfin x hdiam hy)
  rw [norm_integral_eq_volume_mul_average U b hvol] at hle
  convert hle using 1
  field_simp [hvol.ne']

end CoarseDeGiorgi.NegSobolev
