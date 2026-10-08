module

public import CoarseDeGiorgi.Foundations.Reconstruction.ProjectionNesting
public import CoarseDeGiorgi.Foundations.Reconstruction.AuxProjection

/-! # Euclidean vector contraction for triadic averages -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- Change the norm on the coordinate carrier to its Euclidean norm. -/
def euclidLinear : Vec d →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap

theorem norm_euclidLinear (v : Vec d) : ‖euclidLinear v‖ = euclidNorm v :=
  (Euclid.eNorm2_eq_norm_toLp v).symm

theorem cubeAverageVec_eq_integral (Q : TriadicCube d) (f : Vec d → Vec d)
    (hf : IntegrableOn f (cubeSet Q) volume) :
    cubeAverageVec Q f = ∫ x, f x ∂normalizedCubeMeasure Q := by
  have hμ : Integrable f (normalizedCubeMeasure Q) := hf.smul_measure ENNReal.ofReal_ne_top
  funext i
  rw [show cubeAverageVec Q f i = cubeAverage Q (fun x => f x i) from rfl,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  exact (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).integral_comp_comm hμ

/-- Jensen's inequality for the exact Euclidean vector length. -/
theorem euclidNorm_cubeAverageVec_le (Q : TriadicCube d) (f : Vec d → Vec d)
    (hf : IntegrableOn f (cubeSet Q) volume) :
    euclidNorm (cubeAverageVec Q f) ≤ cubeAverage Q (fun x => euclidNorm (f x)) := by
  have hμ : Integrable f (normalizedCubeMeasure Q) := hf.smul_measure ENNReal.ofReal_ne_top
  rw [cubeAverageVec_eq_integral Q f hf, ← norm_euclidLinear,
    ← euclidLinear.integral_comp_comm hμ,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  simpa only [norm_euclidLinear] using
    (norm_integral_le_integral_norm (f := fun x => euclidLinear (f x))
      (μ := normalizedCubeMeasure Q))

/-- Pointwise Jensen on each cell; outside the root both fields vanish. -/
theorem euclidNorm_cubeProjectionVec_le (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (cubeSet Q) volume) (x : Vec d) :
    euclidNorm (cubeProjectionVec Q j f x) ≤
      cubeProjection Q j (fun y => euclidNorm (f y)) x := by
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hx
    rw [cubeProjectionVec_eq_cubeAverageVec_of_mem f hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
    exact euclidNorm_cubeAverageVec_le R f
      (hf.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR))
  · have hz : cubeProjectionVec Q j f x = 0 := by
      funext i
      exact cubeProjection_eq_zero_of_not_mem_cubeSet Q j (fun y => f y i) hx
    rw [hz, cubeProjection_eq_zero_of_not_mem_cubeSet _ _ _ hx]
    exact le_of_eq Euclid.eNorm2_zero

theorem memLp_cubeProjectionVec (Q : TriadicCube d) (j : ℕ) (f : Vec d → Vec d)
    (p : ℝ≥0∞) : MemLp (cubeProjectionVec Q j f) p (normalizedCubeMeasure Q) := by
  classical
  have heq : cubeProjectionVec Q j f = fun x =>
      ∑ R ∈ descendantsAtDepth Q j, (cubeSet R).indicator (fun _ => cubeAverageVec R f) x := by
    funext x i
    simp only [cubeProjectionVec, cubeProjection, Finset.sum_apply, Set.indicator_apply]
    apply Finset.sum_congr rfl
    intro R hR
    split_ifs <;> rfl
  rw [heq]
  exact memLp_finsetSum _ fun R _ => (memLp_const (cubeAverageVec R f)).indicator
    (measurableSet_cubeSet R)

theorem memLp_euclidNorm_cubeProjectionVec (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → Vec d) (p : ℝ≥0∞) :
    MemLp (fun x => euclidNorm (cubeProjectionVec Q j f x)) p
      (normalizedCubeMeasure Q) := by
  have h := memLp_cubeProjectionVec Q j f p
  apply (h.norm.const_mul (Real.sqrt (d : ℝ))).mono'
    (Euclid.continuous_eNorm2.comp_aestronglyMeasurable h.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Euclid.eNorm2_nonneg _)]
    exact Euclid.eNorm2_le_sqrt_mul_norm _

/-- Vector averaging is an Lᵖ contraction for Euclidean length. -/
theorem eLpNorm_euclidNorm_cubeProjectionVec_le (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (cubeSet Q) volume) (p : ℝ≥0∞)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (hmem : MemLp (fun x => euclidNorm (f x)) p (normalizedCubeMeasure Q)) :
    eLpNorm (fun x => euclidNorm (cubeProjectionVec Q j f x)) p (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x => euclidNorm (f x)) p (normalizedCubeMeasure Q) := by
  apply (eLpNorm_mono_ae_real
    (memLp_euclidNorm_cubeProjectionVec Q j f p).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)).trans
    ((ENNReal.toReal_le_toReal (cubeProjection_memLp Q j p _).eLpNorm_ne_top
      hmem.eLpNorm_ne_top).mp (cubeLpNorm_cubeProjection_le Q p _ j hp hpTop hmem))
  rw [Real.norm_eq_abs, euclidNorm_eq_eNorm2, abs_of_nonneg (Euclid.eNorm2_nonneg _)]
  exact euclidNorm_cubeProjectionVec_le Q j f hf x

/-- Euclidean norms of consecutive averaged fields are monotone. -/
theorem eLpNorm_euclidNorm_cubeProjectionVec_mono (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (cubeSet Q) volume)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    eLpNorm (fun x => euclidNorm (cubeProjectionVec Q j f x)) p (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x => euclidNorm (cubeProjectionVec Q (j + 1) f x)) p
        (normalizedCubeMeasure Q) := by
  have hi : IntegrableOn (cubeProjectionVec Q (j + 1) f) (cubeSet Q) volume := by
    exact integrable_pi_iff.mpr fun i =>
      integrableOn_cubeProjection_of_integrableOn Q (j + 1) (fun x => f x i)
  have h := eLpNorm_euclidNorm_cubeProjectionVec_le Q j (cubeProjectionVec Q (j + 1) f)
    hi p hp hpTop (memLp_euclidNorm_cubeProjectionVec Q (j + 1) f p)
  rwa [cubeProjectionVec_nesting Q j f hf] at h

/-- Euclidean Minkowski, with no dimension loss from the ambient sup norm. -/
theorem eLpNorm_euclidNorm_sub_le {μ : Measure (Vec d)} (f g : Vec d → Vec d)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) :
    eLpNorm (fun x => euclidNorm (f x - g x)) p μ ≤
      eLpNorm (fun x => euclidNorm (f x)) p μ +
        eLpNorm (fun x => euclidNorm (g x)) p μ := by
  have hfm : AEStronglyMeasurable (fun x => euclidNorm (f x)) μ :=
    Euclid.continuous_eNorm2.comp_aestronglyMeasurable hf
  have hgm : AEStronglyMeasurable (fun x => euclidNorm (g x)) μ :=
    Euclid.continuous_eNorm2.comp_aestronglyMeasurable hg
  have hsub : AEStronglyMeasurable (fun x => euclidNorm (f x - g x)) μ :=
    Euclid.continuous_eNorm2.comp_aestronglyMeasurable (hf.sub hg)
  apply (eLpNorm_mono_ae_real hsub (ae_of_all _ fun x => ?_)).trans
    (eLpNorm_add_le (f := fun x => euclidNorm (f x)) (g := fun x => euclidNorm (g x)) hp)
  rw [Real.norm_eq_abs, euclidNorm_eq_eNorm2, abs_of_nonneg (Euclid.eNorm2_nonneg _)]
  have h := Euclid.eNorm2_add_le (f x) (-g x)
  simpa only [Pi.add_apply, euclidNorm_eq_eNorm2, sub_eq_add_neg,
    Euclid.eNorm2_eq_norm_toLp, WithLp.toLp_neg, norm_neg] using h

end

end CoarseDeGiorgi.Foundations.Reconstruction
