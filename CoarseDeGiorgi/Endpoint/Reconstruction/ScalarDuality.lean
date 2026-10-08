module

public import CoarseDeGiorgi.Endpoint.Reconstruction.PartitionLp

/-! # Scalar finite-exponent duality using an explicit norming test -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open MeasureTheory
open scoped ENNReal

noncomputable section

def scalarNormingTest {α : Type*} (r : ℝ) (f : α → ℝ) : α → ℝ :=
  fun x => ‖f x‖ ^ (r - 2) * f x

theorem norm_scalarNormingTest {α : Type*} {r : ℝ} (hr : 1 < r)
    (f : α → ℝ) (x : α) :
    ‖scalarNormingTest r f x‖ = ‖f x‖ ^ (r - 1) := by
  rw [scalarNormingTest, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc
    _ = ‖f x‖ ^ (r - 2) * ‖f x‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = ‖f x‖ ^ ((r - 2) + 1) := (Real.rpow_add' (norm_nonneg _) (by linarith)).symm
    _ = _ := by congr 1; ring

theorem mul_scalarNormingTest {α : Type*} {r : ℝ} (hr : 1 < r)
    (f : α → ℝ) (x : α) :
    f x * scalarNormingTest r f x = ‖f x‖ ^ r := by
  have hsquare : f x * f x = ‖f x‖ ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
    ring
  calc
    _ = ‖f x‖ ^ (r - 2) * (f x * f x) := by dsimp [scalarNormingTest]; ring
    _ = ‖f x‖ ^ (r - 2) * ‖f x‖ ^ (2 : ℝ) := by rw [hsquare]
    _ = ‖f x‖ ^ ((r - 2) + 2) := (Real.rpow_add' (norm_nonneg _) (by linarith)).symm
    _ = _ := by congr 1; ring

theorem aestronglyMeasurable_scalarNormingTest {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (r : ℝ) :
    AEStronglyMeasurable (scalarNormingTest r f) μ :=
  (hf.norm.aemeasurable.pow_const (r - 2)).aestronglyMeasurable.mul hf

theorem eLpNorm_scalarNormingTest {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    {r : ℝ} (hr : 1 < r) (p : ℝ≥0∞) :
    eLpNorm (scalarNormingTest r f) p μ =
      eLpNorm f (p * ENNReal.ofReal (r - 1)) μ ^ (r - 1) := by
  rw [eLpNorm_congr_norm_ae (aestronglyMeasurable_scalarNormingTest hf r)
      (hf.norm.aemeasurable.pow_const (r - 1)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [norm_scalarNormingTest hr, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]),
    eLpNorm_norm_rpow f hf (sub_pos.mpr hr)]

/-- Every scalar `L²` function on a finite measure admits its exact norming
function as an admissible `L² ∩ L^{r'}` test when `1 < r < 2`. -/
theorem scalar_lp_duality_of_memL2 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    {r s : ℝ} (hrs : r.HolderConjugate s) (hr2 : r < 2)
    (hf2 : MemLp f 2 μ) {K : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ g : α → ℝ, MemLp g 2 μ → MemLp g (ENNReal.ofReal s) μ →
      |∫ x, f x * g x ∂μ| ≤ K * (eLpNorm g (ENNReal.ofReal s) μ).toReal) :
    eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal K := by
  have hfr : MemLp f (ENNReal.ofReal r) μ := hf2.mono_exponent (by
    exact (ENNReal.ofReal_le_ofReal hr2.le).trans_eq (by norm_num))
  let g := scalarNormingTest r f
  have hsprod : ENNReal.ofReal s * ENNReal.ofReal (r - 1) = ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_mul hrs.symm.pos.le]
    congr 1
    nlinarith [hrs.sub_one_mul_conj]
  have hg2 : MemLp g 2 μ := by
    rw [MemLp, eLpNorm_scalarNormingTest hf2.aestronglyMeasurable hrs.lt]
    apply ENNReal.rpow_lt_top_of_nonneg hrs.sub_one_pos.le
    exact (hf2.mono_exponent (by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by linarith))).eLpNorm_ne_top
  have hgs : MemLp g (ENNReal.ofReal s) μ := by
    rw [MemLp, eLpNorm_scalarNormingTest hf2.aestronglyMeasurable hrs.lt, hsprod]
    exact ENNReal.rpow_lt_top_of_nonneg hrs.sub_one_pos.le hfr.eLpNorm_ne_top
  have htest := hpair g hg2 hgs
  have hintegral : ∫ x, ‖f x‖ ^ r ∂μ = (eLpNorm f (ENNReal.ofReal r) μ).toReal ^ r := by
    have heq := hfr.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_pos.mpr hrs.pos).ne' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hrs.pos.le] at heq
    have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ r ∂μ := integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _
    rw [heq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _),
      ← Real.rpow_mul hnonneg, inv_mul_cancel₀ hrs.ne_zero, Real.rpow_one]
  have hgnorm : (eLpNorm g (ENNReal.ofReal s) μ).toReal =
      (eLpNorm f (ENNReal.ofReal r) μ).toReal ^ (r - 1) := by
    rw [eLpNorm_scalarNormingTest hf2.aestronglyMeasurable hrs.lt, hsprod,
      ← ENNReal.toReal_rpow]
  have hnonneg := ENNReal.toReal_nonneg (a := eLpNorm f (ENNReal.ofReal r) μ)
  simp only [g, mul_scalarNormingTest hrs.lt] at htest
  rw [hintegral, abs_of_nonneg (Real.rpow_nonneg hnonneg _), hgnorm] at htest
  have hreal : (eLpNorm f (ENNReal.ofReal r) μ).toReal ≤ K := by
    by_cases hz : (eLpNorm f (ENNReal.ofReal r) μ).toReal = 0
    · simpa only [hz] using hK
    have hpos := lt_of_le_of_ne hnonneg (Ne.symm hz)
    have hfac : (eLpNorm f (ENNReal.ofReal r) μ).toReal ^ r =
        (eLpNorm f (ENNReal.ofReal r) μ).toReal *
          (eLpNorm f (ENNReal.ofReal r) μ).toReal ^ (r - 1) := by
      have h := Real.rpow_add hpos (1 : ℝ) (r - 1)
      simpa only [show (1 : ℝ) + (r - 1) = r by ring, Real.rpow_one] using h
    rw [hfac] at htest
    have hpow := Real.rpow_pos_of_pos hpos (r - 1)
    nlinarith
  exact (ENNReal.le_ofReal_iff_toReal_le hfr.eLpNorm_ne_top hK).mpr hreal

end

end CoarseDeGiorgi.Endpoint.Reconstruction
