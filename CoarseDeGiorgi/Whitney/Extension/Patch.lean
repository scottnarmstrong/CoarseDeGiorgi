module

public import CoarseDeGiorgi.Whitney.Extension.Geometry

/-!
# Boundary patches `Σ_z` and `Σ_D`
-/

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open Homogenization MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

variable {d : ℕ} {τ h : ℝ}

/-- The patch `Σ_D = ∂(τ□₀) ∩ B(y_{x_D}, √d ℓ(D))` of the paper. -/
def sigmaD (τ : ℝ) (D : TriadicCube d) : Set (Vec d) :=
  cubeSurface τ ∩ {x | euclidDist x (seedProjection τ (triadicCenter D)) <
    Real.sqrt (d : ℝ) * cubeScaleFactor D}

theorem continuous_euclidDist_right (z : Vec d) : Continuous (fun x => euclidDist x z) :=
  Foundations.Euclid.continuous_eNorm2.comp (continuous_id.sub continuous_const)

theorem measurableSet_whitneyPatch (τ : ℝ) (z : Vec d) : MeasurableSet (whitneyPatch τ z) := by
  apply MeasurableSet.inter
  · exact (isClosed_eq continuous_norm continuous_const).measurableSet
  · exact (isOpen_lt (continuous_euclidDist_right _) continuous_const).measurableSet

theorem measurableSet_sigmaD (τ : ℝ) (D : TriadicCube d) : MeasurableSet (sigmaD τ D) := by
  apply MeasurableSet.inter
  · exact (isClosed_eq continuous_norm continuous_const).measurableSet
  · exact (isOpen_lt (continuous_euclidDist_right _) continuous_const).measurableSet

theorem whitneyPatch_subset_surface (τ : ℝ) (z : Vec d) : whitneyPatch τ z ⊆ cubeSurface τ :=
  inter_subset_left

theorem euclidDist_center_le {D : TriadicCube d} {z : Vec d} (hz : z ∈ closedTriadicCube D) :
    euclidDist z (triadicCenter D) ≤ Real.sqrt (d : ℝ) * (cubeScaleFactor D / 2) := by
  refine (euclidDist_le_sqrt_mul z _).trans
    (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  apply (pi_norm_le_iff_of_nonneg (by have := cubeScaleFactor_pos D; linarith only [this])).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using hz i

theorem whitneyPatch_subset_sigmaD (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ) {z : Vec d}
    (hz : z ∈ closedTriadicCube D) : whitneyPatch τ z ⊆ sigmaD τ D := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  have hp := cubeScaleFactor_pos D
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hdr
  have hc : triadicCenter D ∈ closedTriadicCube D := fun i => by
    simp only [sub_self, abs_zero]; linarith only [hp]
  have h1 : euclidDist (seedProjection τ z) (seedProjection τ (triadicCenter D)) ≤
      Real.sqrt (d : ℝ) * (cubeScaleFactor D / 2) :=
    (seedProjection_euclidDist_le τ z _).trans (euclidDist_center_le hz)
  have h2 := hy.2
  simp only [mem_ofPred_eq] at h2 ⊢
  have h3 := gap_upper hτ0 hτ1 hD hz
  have h4 : (‖z‖ - τ / 2) / (100 * (d : ℝ)) ≤ 9 * cubeScaleFactor D / 100 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hp, hdr]
  have h5 := euclidDist_triangle y (seedProjection τ z) (seedProjection τ (triadicCenter D))
  nlinarith [hp, hs1]

/-- Area of a patch at a point of a Whitney cube: `μ(Σ_z) ≥ (ℓ(D)/(100 d²))^(d-1)`. -/
theorem whitneyPatch_measure_lower (hd : 1 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes (d := d) τ) {z : Vec d}
    (hz : z ∈ closedTriadicCube D) (hl : cubeScaleFactor D < 1) :
    ENNReal.ofReal (cubeScaleFactor D / (100 * (d : ℝ) ^ 2)) ^ (d - 1) ≤
      surfaceMeasure τ (whitneyPatch τ z) := by
  have hp := cubeScaleFactor_pos D
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith only [hdr]
  have hlow := gap_lower hτ0 hτ1 hD hz
  have hup := gap_upper hτ0 hτ1 hD hz
  have hnz : τ / 2 ≤ ‖z‖ := by linarith only [hlow, hp]
  set u := (‖z‖ - τ / 2) / (100 * (d : ℝ)) with hu
  have hu0 : 0 < u := by
    apply div_pos _ (by positivity)
    linarith only [hlow, hp]
  have hu1 : u < τ / 2 := by
    rw [hu, div_lt_iff₀ (by positivity)]
    nlinarith [hdr, hl, hup, hτ0]
  have hmem := seedProjection_mem_surface (d := d) (by linarith only [hτ0]) hnz
  have hbound := seedSurfaceMeasure_euclidPatch_lower hu0 hu1 hmem
  refine le_trans ?_ hbound
  apply ENNReal.pow_le_pow_left
  apply ENNReal.ofReal_le_ofReal
  have h2 : cubeScaleFactor D / (100 * (d : ℝ) ^ 2) ≤ u / (2 * d) := by
    rw [hu, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hlow, hp, hdr, mul_pos hdp hdp]
  exact h2

end

end CoarseDeGiorgi.WhitneyExt
