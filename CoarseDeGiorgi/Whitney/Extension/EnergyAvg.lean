import CoarseDeGiorgi.Whitney.Extension.EnergyCell
import CoarseDeGiorgi.Statements.FracKernelWithDimension

/-!
# Jensen bounds for the patch means of a near Whitney cube
-/

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

/-- The `L^b` mass of `f` on `Σ_D`. -/
def locMass (τ : ℝ) (f : Vec d → ℝ) (b : ℝ) (D : TriadicCube d) : ℝ≥0∞ :=
  ∫⁻ x in sigmaD τ D, ENNReal.ofReal (|f x| ^ b) ∂surfaceMeasure τ

/-- The fractional energy of `f` on `Σ_D × Σ_D`. -/
def locFrac (τ α ξ : ℝ) (f : Vec d → ℝ) (D : TriadicCube d) : ℝ≥0∞ :=
  ∫⁻ p in sigmaD τ D ×ˢ sigmaD τ D, fracKernelWithDimension ((d : ℝ) - 1) α ξ f p
    ∂((surfaceMeasure τ).prod (surfaceMeasure τ))

/-- The lower bound for the area of a patch. -/
def mLow (d : ℕ) (ℓ : ℝ) : ℝ := (ℓ / (100 * (d : ℝ) ^ 2)) ^ (d - 1)

theorem mLow_pos (d : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hd : 1 ≤ d) : 0 < mLow d ℓ := by
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold mLow; positivity

theorem ofReal_mLow (d : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ENNReal.ofReal (mLow d ℓ) = ENNReal.ofReal (ℓ / (100 * (d : ℝ) ^ 2)) ^ (d - 1) := by
  unfold mLow
  rw [ENNReal.ofReal_pow]
  by_cases hd : d = 0
  · simp [hd]
  · have : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    positivity

theorem fracKernel_bound {α r D : ℝ} (hr : 0 < r) (hD : 0 < D)
    (hq : 0 ≤ (d : ℝ) - 1 + α * r) (f : Vec d → ℝ) {x y : Vec d}
    (hxy : euclidDist x y ≤ D) :
    ENNReal.ofReal (|f x - f y| ^ r) ≤ ENNReal.ofReal (D ^ ((d : ℝ) - 1 + α * r)) *
      fracKernelWithDimension ((d : ℝ) - 1) α r f (x, y) := by
  by_cases he : x = y
  · subst y
    simp only [sub_self, abs_zero, Real.zero_rpow (ne_of_gt hr), ENNReal.ofReal_zero]
    exact bot_le
  · have hdist : 0 < euclidDist x y := by
      unfold euclidDist
      apply Real.sqrt_pos.mpr
      have := Foundations.Euclid.eDist2_pos he
      unfold Foundations.Euclid.eDist2 Foundations.Euclid.eNorm2 at this
      exact Real.sqrt_pos.mp this
    have hpow : 0 < euclidDist x y ^ ((d : ℝ) - 1 + α * r) := Real.rpow_pos_of_pos hdist _
    have hmono := Real.rpow_le_rpow hdist.le hxy hq
    have hnum : 0 ≤ |f x - f y| ^ r := Real.rpow_nonneg (abs_nonneg _) _
    have hratio : 0 ≤ |f x - f y| ^ r / euclidDist x y ^ ((d : ℝ) - 1 + α * r) :=
      div_nonneg hnum hpow.le
    have hb : |f x - f y| ^ r ≤ D ^ ((d : ℝ) - 1 + α * r) *
        (|f x - f y| ^ r / euclidDist x y ^ ((d : ℝ) - 1 + α * r)) := by
      calc
        _ = euclidDist x y ^ ((d : ℝ) - 1 + α * r) *
            (|f x - f y| ^ r / euclidDist x y ^ ((d : ℝ) - 1 + α * r)) := by
          field_simp [ne_of_gt hpow]
        _ ≤ _ := mul_le_mul_of_nonneg_right hmono hratio
    simpa only [fracKernelWithDimension, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)] using
      ENNReal.ofReal_le_ofReal hb

/-- Jensen for the mean over `Σ_z`. -/
theorem avg_rpow_le (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) (hl : cubeScaleFactor D < 1) {z : Vec d}
    (hz : z ∈ closedTriadicCube D) {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) {b : ℝ}
    (hb : 1 ≤ b) :
    ENNReal.ofReal (|patchAvg τ f z| ^ b) ≤
      (ENNReal.ofReal (mLow d (cubeScaleFactor D)))⁻¹ * locMass τ f b D := by
  have hp := cubeScaleFactor_pos D
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  have h1 := ofReal_abs_average_rpow_le hτ hb (measurableSet_whitneyPatch τ z) hf
  refine h1.trans ?_
  apply mul_le_mul'
  · apply ENNReal.inv_le_inv.mpr
    rw [ofReal_mLow d hp]
    exact whitneyPatch_measure_lower hd hτ0 hτ1 hD hz hl
  · exact lintegral_mono_set (whitneyPatch_subset_sigmaD hd hτ0 hτ1 hD hz)

/-- Jensen for the difference of two means. -/
theorem avg_sub_rpow_le (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {D : TriadicCube d}
    (hD : D ∈ whitneyCubes (d := d) τ) (hl : cubeScaleFactor D < 1) {z z' : Vec d}
    (hz : z ∈ closedTriadicCube D) (hz' : z' ∈ closedTriadicCube D) {f : Vec d → ℝ}
    (hf : ContinuousOn f (cubeSurface τ)) {α ξ : ℝ} (hα : 0 < α) (hξ : 1 ≤ ξ) :
    ENNReal.ofReal (|patchAvg τ f z - patchAvg τ f z'| ^ ξ) ≤
      ((ENNReal.ofReal (mLow d (cubeScaleFactor D))) * ENNReal.ofReal (mLow d (cubeScaleFactor D)))⁻¹ *
        (ENNReal.ofReal ((2 * Real.sqrt (d : ℝ) * cubeScaleFactor D) ^ ((d : ℝ) - 1 + α * ξ)) *
          locFrac τ α ξ f D) := by
  have hp := cubeScaleFactor_pos D
  have hτ : 0 ≤ τ := by linarith only [hτ0]
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := ofReal_abs_average_sub_rpow_le hτ hξ (measurableSet_whitneyPatch τ z)
    (whitneyPatch_subset_surface τ z) (whitneyPatch_measure_pos hd hτ0 hτ1 hD hz hl)
    (measurableSet_whitneyPatch τ z') (whitneyPatch_subset_surface τ z')
    (whitneyPatch_measure_pos hd hτ0 hτ1 hD hz' hl) hf
  refine h1.trans ?_
  apply mul_le_mul'
  · apply ENNReal.inv_le_inv.mpr
    rw [ofReal_mLow d hp]
    exact mul_le_mul' (whitneyPatch_measure_lower hd hτ0 hτ1 hD hz hl)
      (whitneyPatch_measure_lower hd hτ0 hτ1 hD hz' hl)
  · have hS : MeasurableSet (sigmaD τ D ×ˢ sigmaD τ D) :=
      (measurableSet_sigmaD τ D).prod (measurableSet_sigmaD τ D)
    have hq : 0 ≤ (d : ℝ) - 1 + α * ξ := by
      have := mul_pos hα (by linarith only [hξ] : (0 : ℝ) < ξ)
      linarith only [hdr, this]
    have hΔ : 0 < 2 * Real.sqrt (d : ℝ) * cubeScaleFactor D := by
      have : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by linarith only [hdr])
      positivity
    calc _ ≤ ∫⁻ p in sigmaD τ D ×ˢ sigmaD τ D, ENNReal.ofReal (|f p.1 - f p.2| ^ ξ)
            ∂((surfaceMeasure τ).prod (surfaceMeasure τ)) :=
          lintegral_mono_set (Set.prod_mono (whitneyPatch_subset_sigmaD hd hτ0 hτ1 hD hz)
            (whitneyPatch_subset_sigmaD hd hτ0 hτ1 hD hz'))
      _ ≤ ∫⁻ p in sigmaD τ D ×ˢ sigmaD τ D,
            ENNReal.ofReal ((2 * Real.sqrt (d : ℝ) * cubeScaleFactor D) ^ ((d : ℝ) - 1 + α * ξ)) *
              fracKernelWithDimension ((d : ℝ) - 1) α ξ f p
            ∂((surfaceMeasure τ).prod (surfaceMeasure τ)) := by
          apply setLIntegral_mono' hS
          intro p hp'
          exact fracKernel_bound (by linarith only [hξ]) hΔ hq f (sigmaD_dist_le hp'.1 hp'.2)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end

end CoarseDeGiorgi.WhitneyExt
