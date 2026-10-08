import CoarseDeGiorgi.NegSobolev.GaussianBasic
import CoarseDeGiorgi.Statements.OriginCube
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Positivity of entrywise Gaussian matrix averages -/

open Homogenization MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- Entrywise integrability suffices to commute a quadratic form with the integral. -/
theorem quadratic_integral_eq {d : ℕ} {μ : Measure (Vec d)} (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) μ) (e : Vec d) :
    dotProduct e ((Matrix.of fun i j => ∫ x, b x i j ∂μ).mulVec e) =
      ∫ x, dotProduct e ((b x).mulVec e) ∂μ := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((hb i j).mul_const (e j)).const_mul (e i)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => ((hb i j).mul_const (e j)).const_mul (e i))]
  simp only [integral_const_mul, integral_mul_const]

/-- Entrywise integrals preserve the cone of positive semidefinite matrices. -/
theorem integral_matrix_posSemidef {d : ℕ} {μ : Measure (Vec d)} (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) μ)
    (hpos : ∀ᵐ x ∂μ, (b x).PosSemidef) :
    (Matrix.of fun i j => ∫ x, b x i j ∂μ).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    exact hx.isHermitian.apply i j
  · intro e
    simp only [star_trivial]
    rw [quadratic_integral_eq b hb e]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    exact hx.dotProduct_mulVec_nonneg e

/-- The entrywise volume average of a positive semidefinite field is positive semidefinite. -/
theorem volumeAverageMat_posSemidef {d : ℕ} (U : Set (Vec d)) (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (hpos : ∀ᵐ x ∂(volume.restrict U), (b x).PosSemidef) :
    (volumeAverageMat U b).PosSemidef := by
  have h := integral_matrix_posSemidef b hb hpos
  exact h.smul (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- Quadratic forms of the field are integrable when all entries are integrable. -/
theorem quadratic_integrable {d : ℕ} {μ : Measure (Vec d)} (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) μ) (e : Vec d) :
    Integrable (fun x => dotProduct e ((b x).mulVec e)) μ := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => ((hb i j).mul_const (e j)).const_mul (e i)))

/-- A bounded Gaussian multiplier preserves entrywise integrability. -/
theorem integrable_gaussianKernel_mul {d : ℕ} (t : ℝ) (ht : 0 < t)
    (x : Vec d) {f : Vec d → ℝ} (hf : Integrable f volume) :
    Integrable (fun y => gaussianKernel t ht (x - y) * f y) volume := by
  refine hf.bdd_mul (f := fun y => gaussianKernel t ht (x - y))
    (c := (4 * Real.pi * t) ^ (-((d : ℝ) / 2))) ?_ ?_
  · exact ((continuous_gaussianKernel t ht).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  rw [Real.norm_of_nonneg (gaussianKernel_nonneg t ht (x - y))]
  exact gaussianKernel_le_prefactor t ht (x - y)

/-- Gaussian convolution preserves positive semidefiniteness everywhere. -/
theorem gaussianKernel_convolution_posSemidef {d : ℕ} (t : ℝ) (ht : 0 < t)
    (b : Vec d → Mat d) (hb : ∀ i j, Integrable (fun y => b y i j) volume)
    (hpos : ∀ᵐ y ∂volume, (b y).PosSemidef) (x : Vec d) :
    (Matrix.of fun i j => ∫ y, gaussianKernel t ht (x - y) * b y i j).PosSemidef := by
  apply integral_matrix_posSemidef (fun y => gaussianKernel t ht (x - y) • b y)
    (fun i j => integrable_gaussianKernel_mul t ht x (hb i j))
  filter_upwards [hpos] with y hy
  exact hy.smul (gaussianKernel_nonneg t ht (x - y))

/-- Zero extension preserves positive semidefiniteness. -/
theorem indicator_matrix_posSemidef {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (b : Vec d → Mat d) (hpos : ∀ᵐ y ∂(volume.restrict U), (b y).PosSemidef) :
    ∀ᵐ y ∂volume, (U.indicator b y).PosSemidef := by
  classical
  rw [ae_restrict_iff' hU] at hpos
  filter_upwards [hpos] with y hy
  by_cases hyU : y ∈ U
  · rw [Set.indicator_of_mem hyU]
    exact hy hyU
  · rw [Set.indicator_of_notMem hyU]
    exact Matrix.PosSemidef.zero

/-- Coordinate evaluation commutes with zero extension. -/
theorem indicator_matrix_apply {d : ℕ} (U : Set (Vec d)) (b : Vec d → Mat d)
    (i j : Fin d) (y : Vec d) :
    U.indicator b y i j = U.indicator (fun z => b z i j) y := by
  classical
  by_cases hy : y ∈ U
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, Matrix.zero_apply]

/-- Entrywise integrable fields have entrywise integrable zero extensions. -/
theorem integrable_indicator_matrix_entry {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun y => b y i j) (volume.restrict U)) (i j : Fin d) :
    Integrable (fun y => U.indicator b y i j) volume := by
  simp_rw [indicator_matrix_apply]
  exact IntegrableOn.integrable_indicator (hb i j) hU

/-- In particular Gaussian convolution of a zero-extended positive field is
positive semidefinite at every point, under the source's entrywise `L¹` premise. -/
theorem gaussianKernel_indicator_convolution_posSemidef {d : ℕ}
    (t : ℝ) (ht : 0 < t) {U : Set (Vec d)} (hU : MeasurableSet U)
    (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun y => b y i j) (volume.restrict U))
    (hpos : ∀ᵐ y ∂(volume.restrict U), (b y).PosSemidef) (x : Vec d) :
    (Matrix.of fun i j => ∫ y, gaussianKernel t ht (x - y) * U.indicator b y i j).PosSemidef :=
  gaussianKernel_convolution_posSemidef t ht (U.indicator b)
    (integrable_indicator_matrix_entry hU b hb) (indicator_matrix_posSemidef hU b hpos) x

/-- Gaussian matrix averages are a.e. strongly measurable from entrywise `L¹` data. -/
theorem aestronglyMeasurable_gaussianKernel_matrix {d : ℕ}
    (t : ℝ) (ht : 0 < t) (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun y => b y i j) volume) :
    AEStronglyMeasurable (fun x => Matrix.of fun i j =>
      ∫ y, gaussianKernel t ht (x - y) * b y i j) volume := by
  have hk : Continuous (fun z : Vec d × Vec d => gaussianKernel t ht (z.1 - z.2)) :=
    (continuous_gaussianKernel t ht).comp (continuous_fst.sub continuous_snd)
  have he (i j : Fin d) : AEStronglyMeasurable
      (fun x => ∫ y, gaussianKernel t ht (x - y) * b y i j) volume :=
    (hk.stronglyMeasurable.aestronglyMeasurable.mul
      (hb i j).aestronglyMeasurable.comp_snd).integral_prod_right'
  exact (AEMeasurable.of_eval (fun i => AEMeasurable.of_eval
    (fun j => (he i j).aemeasurable))).aestronglyMeasurable

/-- Zero extension changes the whole-space matrix heat integral into a set integral. -/
theorem gaussianKernel_indicator_entry_eq {d : ℕ} (t : ℝ) (ht : 0 < t)
    (U : Set (Vec d)) (hU : MeasurableSet U) (b : Vec d → Mat d)
    (x : Vec d) (i j : Fin d) :
    (∫ y, gaussianKernel t ht (x - y) * U.indicator b y i j) =
      ∫ y in U, gaussianKernel t ht (x - y) * b y i j := by
  classical
  have heq : (fun y => gaussianKernel t ht (x - y) * U.indicator b y i j) =
      U.indicator (fun y => gaussianKernel t ht (x - y) * b y i j) := by
    funext y
    by_cases hy : y ∈ U
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy, Matrix.zero_apply, mul_zero]
  rw [heq, integral_indicator hU]

/-- The set-integral formulation of the matrix heat field is a.e. strongly measurable. -/
theorem aestronglyMeasurable_gaussianKernel_set_matrix {d : ℕ}
    (t : ℝ) (ht : 0 < t) (U : Set (Vec d)) (hU : MeasurableSet U) (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun y => b y i j) (volume.restrict U)) :
    AEStronglyMeasurable (fun x => Matrix.of fun i j =>
      ∫ y in U, gaussianKernel t ht (x - y) * b y i j) volume := by
  have h := aestronglyMeasurable_gaussianKernel_matrix t ht (U.indicator b)
    (integrable_indicator_matrix_entry hU b hb)
  simp_rw [gaussianKernel_indicator_entry_eq t ht U hU b] at h
  exact h

/-- Zero extension does not alter the average on a measurable subset of its carrier. -/
theorem volumeAverageMat_indicator_of_subset {d : ℕ} (U V : Set (Vec d))
    (hU : MeasurableSet U) (hUV : U ⊆ V) (b : Vec d → Mat d) :
    volumeAverageMat U (V.indicator b) = volumeAverageMat U b := by
  classical
  ext i j
  unfold volumeAverageMat volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU] with y hy
  rw [Set.indicator_of_mem (hUV hy)]

end CoarseDeGiorgi.NegSobolev
