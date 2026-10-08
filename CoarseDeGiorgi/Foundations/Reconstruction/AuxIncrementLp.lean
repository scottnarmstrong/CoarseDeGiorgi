module

public import CoarseDeGiorgi.Foundations.Reconstruction.VectorProjectionLp
public import CoarseDeGiorgi.Foundations.Reconstruction.ReflectedAverages

/-! # Euclidean Lᵖ bounds for exact auxiliary and reflected increments -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem auxAverage_add_eq_cubeProjectionVec_ae (m : ℤ) (j : ℕ)
    (z : Fin d → ℤ) (f : Vec d → Vec d) :
    (fun y => auxAverage m (m + j) z f (y + auxCenter m z)) =ᵐ[volume]
      cubeProjectionVec (originCube d (1 - m)) j (fun y => f (y + auxCenter m z)) := by
  have h := ae_all_iff.mpr fun i : Fin d =>
    auxAverage_add_eq_cubeProjection_ae m (m + j) (by omega) z f i
  filter_upwards [h] with y hy
  funext i
  simpa only [add_sub_cancel_left, Int.toNat_natCast, cubeProjectionVec] using hy i

/-- Finite positive normalization does not change comparisons of Lᵖ norms. -/
theorem eLpNorm_normalizedCubeMeasure_le_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (Q : TriadicCube d) (f : Vec d → E) (g : Vec d → F) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm f p (normalizedCubeMeasure Q) ≤ eLpNorm g p (normalizedCubeMeasure Q) ↔
      eLpNorm f p (volume.restrict (cubeSet Q)) ≤
        eLpNorm g p (volume.restrict (cubeSet Q)) := by
  have hc0 : ENNReal.ofReal (cubeVolume Q)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  unfold normalizedCubeMeasure cubeMeasure
  rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hpTop,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hpTop]
  simp only [smul_eq_mul]
  rw [mul_comm _ (eLpNorm f _ _), mul_comm _ (eLpNorm g _ _)]
  exact ENNReal.mul_le_mul_iff_left (by positivity)
    (ENNReal.rpow_ne_top_of_ne_zero hc0 ENNReal.ofReal_ne_top)

/-- Translation and the open/half-open face bridge preserve Euclidean Lᵖ norms. -/
theorem eLpNorm_euclidNorm_auxAverage_eq (m : ℤ) (j : ℕ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (p : ℝ≥0∞) :
    eLpNorm (fun x => euclidNorm (auxAverage m (m + j) z f x)) p
      (volume.restrict (auxCube m z)) =
      eLpNorm (fun x => euclidNorm (cubeProjectionVec (originCube d (1 - m)) j
        (fun y => f (y + auxCenter m z)) x)) p
        (volume.restrict (cubeSet (originCube d (1 - m)))) := by
  let Q := originCube d (1 - m)
  have hμ := measurePreserving_addRight_restrict_translateSet (auxCenter m z) (openCubeSet Q)
  rw [← auxCube_eq_translate_originCube m z] at hμ
  have hmeas := (memLp_euclidNorm_auxAverage m (m + j) z f p).aestronglyMeasurable
  rw [← eLpNorm_comp_measurePreserving hmeas hμ]
  rw [← Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)]
  exact eLpNorm_congr_ae ((auxAverage_add_eq_cubeProjectionVec_ae m j z f).restrict.fun_comp
    euclidNorm)

/-- Consecutive auxiliary average norms are monotone, with only L¹ input. -/
theorem eLpNorm_euclidNorm_auxAverage_mono (m : ℤ) (j : ℕ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    eLpNorm (fun x => euclidNorm (auxAverage m (m + j) z f x)) p
      (volume.restrict (auxCube m z)) ≤
      eLpNorm (fun x => euclidNorm (auxAverage m (m + (j + 1 : ℕ)) z f x)) p
        (volume.restrict (auxCube m z)) := by
  rw [eLpNorm_euclidNorm_auxAverage_eq, eLpNorm_euclidNorm_auxAverage_eq]
  apply (eLpNorm_normalizedCubeMeasure_le_iff _ _ _ p
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpTop).mp
  exact eLpNorm_euclidNorm_cubeProjectionVec_mono _ j _
    (integrableOn_auxCenter_pullback m z f hf) p hp hpTop

/-- The entire reflected vector field is integrable for L¹ input. -/
theorem integrableOn_reflectedGradient {m : ℤ} {z : Fin d → ℤ}
    {f : Vec d → Vec d} (hf : IntegrableOn f (auxCube m z) volume) :
    IntegrableOn (reflectedGradient m z f) (reflectionBox m) volume :=
  integrable_pi_iff.mpr fun i => integrableOn_reflectedPartial hf i

/-- Reflection preserves monotonicity of Euclidean average norms. -/
theorem eLpNorm_euclidNorm_reflectedAverage_mono (m : ℤ) (j : ℕ) (z : Fin d → ℤ)
    (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    eLpNorm (fun x => euclidNorm (reflectedAverage m j z f x)) p
      (volume.restrict (reflectionBox m)) ≤
      eLpNorm (fun x => euclidNorm (reflectedAverage m (j + 1) z f x)) p
        (volume.restrict (reflectionBox m)) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  rw [eLpNorm_euclidNorm_reflectedAverage m j z f p hp0 hpTop,
    eLpNorm_euclidNorm_reflectedAverage m (j + 1) z f p hp0 hpTop]
  exact mul_le_mul_of_nonneg_left (eLpNorm_euclidNorm_auxAverage_mono m j z f hf p hp hpTop) bot_le

/-- The reflected increment has Euclidean Lᵖ norm at most twice the fine average. -/
theorem eLpNorm_euclidNorm_reflectedAverage_increment_le (m : ℤ) (j : ℕ)
    (z : Fin d → ℤ) (f : Vec d → Vec d) (hf : IntegrableOn f (auxCube m z) volume)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ∞) :
    eLpNorm (fun x => euclidNorm (reflectedAverage m (j + 1) z f x -
      reflectedAverage m j z f x)) p (volume.restrict (reflectionBox m)) ≤
      2 * eLpNorm (fun x => euclidNorm (reflectedAverage m (j + 1) z f x)) p
        (volume.restrict (reflectionBox m)) := by
  have hi (k : ℕ) : IntegrableOn (reflectedAverage m k z f) (reflectionBox m) volume :=
    integrableOn_reflectedGradient
      (memLp_one_iff_integrable.mp (memLp_auxAverage m (m + k) z f 1))
  have ht := eLpNorm_euclidNorm_sub_le (reflectedAverage m (j + 1) z f)
    (reflectedAverage m j z f) (hi (j + 1)).aestronglyMeasurable
    (hi j).aestronglyMeasurable p hp
  have hm := eLpNorm_euclidNorm_reflectedAverage_mono m j z f hf p hp hpTop
  exact ht.trans ((add_le_add le_rfl hm).trans_eq (two_mul _).symm)

end

end CoarseDeGiorgi.Foundations.Reconstruction
