module

public import CoarseDeGiorgi.Whitney.Extension.Patch
public import CoarseDeGiorgi.Whitney.Extension.Averages
public import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
public import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
public import CoarseDeGiorgi.Statements.WhitneyInterpolation
public import CoarseDeGiorgi.Statements.EuclidNorm

/-!
# Differences of the free-vertex values

The value `L_h f(z) = ω(...) ⨍_{Σ_z} f` at the free vertices of a near Whitney cube.
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

/-- The mean of `f` over the patch `Σ_z`. -/
def patchAvg (τ : ℝ) (f : Vec d → ℝ) (z : Vec d) : ℝ :=
  ⨍ x in whitneyPatch τ z, f x ∂surfaceMeasure τ

theorem whitneyFreeValue_eq (τ h : ℝ) (f : Vec d → ℝ) (z : {z : Vec d // IsFreeVertex τ z}) :
    whitneyFreeValue τ h f z = seedCutoff ((‖z.1‖ - τ / 2) / h) * patchAvg τ f z.1 := rfl

/-- The decomposition of the difference of two values. -/
theorem freeValue_sub_le (hh : 0 < h) (f : Vec d → ℝ) {D : TriadicCube d}
    {z z' : {z : Vec d // IsFreeVertex τ z}} (hz : z.1 ∈ closedTriadicCube D)
    (hz' : z'.1 ∈ closedTriadicCube D) :
    |whitneyFreeValue τ h f z - whitneyFreeValue τ h f z'| ≤
      2 * cubeScaleFactor D / h * |patchAvg τ f z.1| +
        |patchAvg τ f z.1 - patchAvg τ f z'.1| := by
  rw [whitneyFreeValue_eq, whitneyFreeValue_eq]
  set ω := seedCutoff ((‖z.1‖ - τ / 2) / h)
  set ω' := seedCutoff ((‖z'.1‖ - τ / 2) / h)
  set a := patchAvg τ f z.1
  set a' := patchAvg τ f z'.1
  have h1 : |ω - ω'| ≤ 2 * cubeScaleFactor D / h := by
    have := seedCutoff_abs_sub_le ((‖z.1‖ - τ / 2) / h) ((‖z'.1‖ - τ / 2) / h)
    refine this.trans ?_
    have e : (‖z.1‖ - τ / 2) / h - (‖z'.1‖ - τ / 2) / h = (‖z.1‖ - ‖z'.1‖) / h := by ring
    rw [e, abs_div, abs_of_pos hh, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply div_le_div_of_nonneg_right _ hh.le
    exact (abs_norm_sub_norm_le _ _).trans (norm_sub_le_of_mem_cube hz hz')
  have h2 : |ω'| ≤ 1 := by
    rw [abs_of_nonneg (seedCutoff_nonneg _)]; exact seedCutoff_le_one _
  have e : ω * a - ω' * a' = (ω - ω') * a + ω' * (a - a') := by ring
  rw [e]
  calc |(ω - ω') * a + ω' * (a - a')| ≤ |(ω - ω') * a| + |ω' * (a - a')| := abs_add_le _ _
    _ = |ω - ω'| * |a| + |ω'| * |a - a'| := by rw [abs_mul, abs_mul]
    _ ≤ 2 * cubeScaleFactor D / h * |a| + 1 * |a - a'| := by
        gcongr
    _ = _ := by ring

theorem sigmaD_dist_le {D : TriadicCube d} {x y : Vec d} (hx : x ∈ sigmaD τ D)
    (hy : y ∈ sigmaD τ D) : euclidDist x y ≤ 2 * Real.sqrt (d : ℝ) * cubeScaleFactor D := by
  have h1 := hx.2
  have h2 := hy.2
  simp only [mem_ofPred_eq] at h1 h2
  have := euclidDist_triangle x (seedProjection τ (triadicCenter D)) y
  rw [euclidDist_comm (seedProjection τ (triadicCenter D)) y] at this
  linarith only [this, h1, h2]

theorem whitneyPatch_measure_pos (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ) {z : Vec d}
    (hz : z ∈ closedTriadicCube D) (hl : cubeScaleFactor D < 1) :
    0 < surfaceMeasure τ (whitneyPatch τ z) := by
  have hp := cubeScaleFactor_pos D
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine lt_of_lt_of_le ?_ (whitneyPatch_measure_lower hd hτ0 hτ1 hD hz hl)
  apply ENNReal.pow_pos
  exact ENNReal.ofReal_pos.mpr (by positivity)

/-- Differences of free values for Lipschitz data. -/
theorem freeValue_sub_le_lip (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (hh : 0 < h)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ) (hl : cubeScaleFactor D < 1)
    {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hLip : ∀ x ∈ cubeSurface τ, ∀ y ∈ cubeSurface τ, |f x - f y| ≤ K * euclidDist x y)
    (hbd : ∀ᵐ y ∂surfaceMeasure τ, |f y| ≤ B)
    {z z' : {z : Vec d // IsFreeVertex τ z}} (hz : z.1 ∈ closedTriadicCube D)
    (hz' : z'.1 ∈ closedTriadicCube D) :
    |whitneyFreeValue τ h f z - whitneyFreeValue τ h f z'| ≤
      2 * cubeScaleFactor D / h * B + K * (2 * Real.sqrt (d : ℝ) * cubeScaleFactor D) := by
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  refine (freeValue_sub_le hh f hz hz').trans ?_
  have hp := cubeScaleFactor_pos D
  have ha : |patchAvg τ f z.1| ≤ B := abs_average_le _ hB hbd
  have hdiff : |patchAvg τ f z.1 - patchAvg τ f z'.1| ≤
      K * (2 * Real.sqrt (d : ℝ) * cubeScaleFactor D) := by
    apply abs_average_sub_average_le hτ (measurableSet_whitneyPatch τ _)
      (whitneyPatch_subset_surface τ _) (whitneyPatch_measure_pos hd hτ0 hτ1 hD hz hl)
      (measurableSet_whitneyPatch τ _) (whitneyPatch_subset_surface τ _)
      (whitneyPatch_measure_pos hd hτ0 hτ1 hD hz' hl) hf
    intro x hx y hy
    refine (hLip x (whitneyPatch_subset_surface τ _ hx) y (whitneyPatch_subset_surface τ _ hy)).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK
    exact sigmaD_dist_le (whitneyPatch_subset_sigmaD hd hτ0 hτ1 hD hz hx)
      (whitneyPatch_subset_sigmaD hd hτ0 hτ1 hD hz' hy)
  have : 0 ≤ 2 * cubeScaleFactor D / h := by positivity
  nlinarith [mul_le_mul_of_nonneg_left ha this]

end

end CoarseDeGiorgi.WhitneyExt
