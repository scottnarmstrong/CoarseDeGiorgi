module

public import CoarseDeGiorgi.Foundations.Reconstruction.AuxPartition

/-! # Identifying the auxiliary averages and proving their L¹ convergence -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators Topology ENNReal

noncomputable section

variable {d : ℕ}

theorem auxDescendantCube_add_mem (m k : ℤ) (z n : Fin d → ℤ) (y : Vec d) :
    y + auxCenter m z ∈ auxDescendantCube m k z n ↔
      y ∈ openCubeSet (auxDescendantDescriptor k n) := by
  rw [auxDescendantCube_eq_translate]
  constructor
  · rintro ⟨a, ha, heq⟩
    exact add_right_cancel heq ▸ ha
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- The normalization and integral in an auxiliary average agree exactly with
the corresponding translated triadic average, including its open-face convention. -/
theorem auxDescendantAverage_eq_cubeAverage (m k : ℤ) (z n : Fin d → ℤ)
    (f : Vec d → Vec d) (i : Fin d) :
    auxDescendantAverage m k z n f i =
      cubeAverage (auxDescendantDescriptor k n) (fun y => f (y + auxCenter m z) i) := by
  unfold auxDescendantAverage cubeAverage
  change ((auxSide k) ^ d)⁻¹ * _ = ((auxSide k) ^ d)⁻¹ * _
  congr 1
  rw [setIntegral_congr_set (cubeSet_ae_eq_openCubeSet (auxDescendantDescriptor k n))]
  rw [setIntegral_comp_addRight_translateSet (auxCenter m z)
    (openCubeSet (auxDescendantDescriptor k n)) (fun x => f x i)]
  congr 1
  rw [auxDescendantCube_eq_translate, image_addRight_eq_translateSet]

/-- The copied open-cell step field is a.e. the usual half-open projection.
No measurability assumption on the input is used for this exact identification. -/
theorem auxAverage_add_eq_cubeProjection_ae (m k : ℤ) (hmk : m ≤ k)
    (z : Fin d → ℤ) (f : Vec d → Vec d) (i : Fin d) :
    (fun y => auxAverage m k z f (y + auxCenter m z) i) =ᵐ[volume]
      cubeProjection (originCube d (1 - m)) (k - m).toNat
        (fun y => f (y + auxCenter m z) i) := by
  classical
  have ha : ∀ᵐ y : Vec d ∂volume, ∀ n : Fin d → ℤ,
      y ∈ cubeSet (auxDescendantDescriptor k n) ↔
        y ∈ openCubeSet (auxDescendantDescriptor k n) :=
    ae_all_iff.mpr fun n =>
      (cubeSet_ae_eq_openCubeSet (auxDescendantDescriptor k n)).mono fun _ h => Iff.of_eq h
  filter_upwards [ha] with y hy
  unfold cubeProjection
  rw [descendantsAtDepth_eq_map_auxDescendantIndices m k hmk, Finset.sum_map]
  change (∑ n ∈ auxDescendantIndices m k,
      (if y + auxCenter m z ∈ auxDescendantCube m k z n then
        auxDescendantAverage m k z n f else 0)) i = _
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change (if y + auxCenter m z ∈ auxDescendantCube m k z n then
      auxDescendantAverage m k z n f else 0) i =
    if y ∈ cubeSet (auxDescendantDescriptor k n) then
      cubeAverage (auxDescendantDescriptor k n) (fun y => f (y + auxCenter m z) i) else 0
  rw [auxDescendantCube_add_mem, ← hy n]
  by_cases h : y ∈ cubeSet (auxDescendantDescriptor k n) <;>
    simp only [h, ite_true, ite_false, Pi.zero_apply, auxDescendantAverage_eq_cubeAverage]

/-- Translation transfers L¹ input on the open auxiliary root to the half-open root. -/
theorem integrableOn_auxCenter_pullback {E : Type*} [NormedAddCommGroup E]
    (m : ℤ) (z : Fin d → ℤ) (f : Vec d → E)
    (hf : IntegrableOn f (auxCube m z) volume) :
    IntegrableOn (fun y => f (y + auxCenter m z)) (cubeSet (originCube d (1 - m)))
      volume := by
  rw [integrableOn_congr_set_ae (cubeSet_ae_eq_openCubeSet (originCube d (1 - m)))]
  have hμ := measurePreserving_addRight_restrict_translateSet (auxCenter m z)
    (openCubeSet (originCube d (1 - m)))
  rw [← auxCube_eq_translate_originCube m z] at hμ
  exact hμ.integrable_comp_of_integrable hf

/-- Coordinatewise strong L¹ convergence of the exact auxiliary averages. -/
theorem tendsto_integral_norm_auxAverage_sub_coordinate (m : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume) (i : Fin d) :
    Tendsto (fun j : ℕ => ∫ x in auxCube m z,
      ‖auxAverage m (m + j) z f x i - f x i‖ ∂volume) atTop (𝓝 0) := by
  have hfi : IntegrableOn (fun x => f x i) (auxCube m z) volume := hf.eval i
  have hroot := integrableOn_auxCenter_pullback m z (fun x => f x i) hfi
  have hlim := tendsto_integral_norm_cubeProjection_sub (originCube d (1 - m))
    (fun y => f (y + auxCenter m z) i) hroot
  convert hlim using 1
  ext j
  rw [auxCube_eq_translate_originCube m z, ← setIntegral_comp_addRight_translateSet,
    ← setIntegral_congr_set (cubeSet_ae_eq_openCubeSet (originCube d (1 - m)))]
  apply integral_congr_ae
  have hmk : m ≤ m + (j : ℤ) := by omega
  have ha : (fun y => auxAverage m (m + j) z f (y + auxCenter m z) i) =ᵐ[
      volume.restrict (cubeSet (originCube d (1 - m)))]
      cubeProjection (originCube d (1 - m)) (m + j - m).toNat
        (fun y => f (y + auxCenter m z) i) :=
    (auxAverage_add_eq_cubeProjection_ae m (m + j) hmk z f i).restrict
  filter_upwards [ha] with y hy
  rw [hy]
  simp only [add_sub_cancel_left, Int.toNat_natCast]

/-- Every auxiliary step field has finite Lᵖ norm, even when its input is only L¹. -/
theorem memLp_auxAverage (m k : ℤ) (z : Fin d → ℤ) (f : Vec d → Vec d)
    (p : ℝ≥0∞) : MemLp (auxAverage m k z f) p (volume.restrict (auxCube m z)) := by
  classical
  let : IsFiniteMeasure (volume.restrict (auxCube m z)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_top_iff_ne_top.mpr (volume_auxCube_ne_top m z))⟩
  unfold auxAverage
  apply memLp_finsetSum
  intro n hn
  exact (memLp_const (auxDescendantAverage m k z n f)).indicator
    (measurableSet_auxDescendantCube m k z n)

theorem memLp_euclidNorm_auxAverage (m k : ℤ) (z : Fin d → ℤ) (f : Vec d → Vec d)
    (p : ℝ≥0∞) : MemLp (fun x => euclidNorm (auxAverage m k z f x)) p
      (volume.restrict (auxCube m z)) := by
  apply ((memLp_auxAverage m k z f p).norm.const_mul (Real.sqrt (d : ℝ))).mono'
    (measurable_euclidNorm_auxAverage m k z f).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [euclidNorm_eq_eNorm2, Real.norm_eq_abs, abs_of_nonneg (Euclid.eNorm2_nonneg _)]
    exact Euclid.eNorm2_le_sqrt_mul_norm _

/-- The ambient sup norm is bounded by the sum of the coordinate norms. -/
theorem norm_vec_le_sum_coordinate (v : Vec d) : ‖v‖ ≤ ∑ i : Fin d, ‖v i‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
  intro i
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/-- Strong L¹ convergence for the whole vector field on the exact open root. -/
theorem tendsto_integral_norm_auxAverage_sub (m : ℤ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume) :
    Tendsto (fun j : ℕ => ∫ x in auxCube m z,
      ‖auxAverage m (m + j) z f x - f x‖ ∂volume) atTop (𝓝 0) := by
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin d))
    (fun i _ => tendsto_integral_norm_auxAverage_sub_coordinate m z f hf i)
  have hupper : ∀ j : ℕ, ∫ x in auxCube m z,
      ‖auxAverage m (m + j) z f x - f x‖ ∂volume ≤
        ∑ i : Fin d, ∫ x in auxCube m z,
          ‖auxAverage m (m + j) z f x i - f x i‖ ∂volume := by
    intro j
    have hg : IntegrableOn (auxAverage m (m + j) z f) (auxCube m z) volume :=
      memLp_one_iff_integrable.mp (memLp_auxAverage m (m + j) z f 1)
    have hi : ∀ i : Fin d, IntegrableOn
        (fun x => ‖auxAverage m (m + j) z f x i - f x i‖) (auxCube m z) volume :=
      fun i => ((hg.eval i).sub (hf.eval i)).norm
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    exact integral_mono ((hg.sub hf).norm) (integrable_finsetSum _ (fun i _ => hi i))
      fun x => norm_vec_le_sum_coordinate (auxAverage m (m + j) z f x - f x)
  exact squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) hupper
    (by simpa only [Finset.sum_const_zero] using hlim)

end

end CoarseDeGiorgi.Foundations.Reconstruction
