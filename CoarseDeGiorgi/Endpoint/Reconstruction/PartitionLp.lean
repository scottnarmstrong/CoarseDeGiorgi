import CoarseDeGiorgi.Endpoint.Reconstruction.FineProjection

/-! # Gluing finite-exponent estimates across a finite partition -/

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

theorem eLpNorm_rpow_eq_lintegral_enorm {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpTop : p ≠ ⊤) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf, ← ENNReal.rpow_mul,
    one_div, inv_mul_cancel₀ hpReal.ne', ENNReal.rpow_one]

/-- The same multiplicative bound on each finite partition measure gives the
bound on their sum, without a loss depending on the number of cells. -/
theorem eLpNorm_finsetSum_measure_le {α E F ι : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (s : Finset ι)
    (μ : ι → Measure α) {f : α → E} {g : α → F} {p : ℝ≥0∞} {C : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpTop : p ≠ ⊤)
    (hf : AEStronglyMeasurable f (∑ i ∈ s, μ i))
    (hg : AEStronglyMeasurable g (∑ i ∈ s, μ i))
    (hbound : ∀ i ∈ s, eLpNorm f p (μ i) ≤ C * eLpNorm g p (μ i)) :
    eLpNorm f p (∑ i ∈ s, μ i) ≤ C * eLpNorm g p (∑ i ∈ s, μ i) := by
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hlocal (i : ι) (hi : i ∈ s) :
      (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ i) ≤ C ^ p.toReal * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ i := by
    have hμ : μ i ≤ ∑ j ∈ s, μ j := Finset.single_le_sum (fun _ _ => bot_le) hi
    have hh := ENNReal.rpow_le_rpow (hbound i hi) hpReal.le
    rwa [ENNReal.mul_rpow_of_nonneg _ _ hpReal.le,
      eLpNorm_rpow_eq_lintegral_enorm hp0 hpTop (hf.mono_measure hμ),
      eLpNorm_rpow_eq_lintegral_enorm hp0 hpTop (hg.mono_measure hμ)] at hh
  apply (ENNReal.rpow_le_rpow_iff hpReal).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpReal.le,
    eLpNorm_rpow_eq_lintegral_enorm hp0 hpTop hf,
    eLpNorm_rpow_eq_lintegral_enorm hp0 hpTop hg,
    lintegral_finsetSum_measure, lintegral_finsetSum_measure, Finset.mul_sum]
  exact Finset.sum_le_sum hlocal

theorem volume_restrict_cube_eq_sum_descendants {d : ℕ} (Q : TriadicCube d) (k : ℕ) :
    volume.restrict (cubeSet Q) =
      ∑ R ∈ descendantsAtDepth Q k, volume.restrict (cubeSet R) := by
  rw [cubeSet_eq_iUnion_descendantsAtDepth Q k]
  simp only [Finset.mem_coe]
  rw [Measure.restrict_biUnion_finset (pairwiseDisjoint_descendantsAtDepth Q k)
      (fun R => measurableSet_cubeSet R)]
  exact Measure.sum_coe_finset (descendantsAtDepth Q k) (fun R => volume.restrict (cubeSet R))

theorem volume_restrict_openCube_eq_sum_descendants {d : ℕ} (Q : TriadicCube d) (k : ℕ) :
    volume.restrict (openCubeSet Q) =
      ∑ R ∈ descendantsAtDepth Q k, volume.restrict (openCubeSet R) := by
  rw [← Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q),
    volume_restrict_cube_eq_sum_descendants]
  exact Finset.sum_congr rfl fun R _ =>
    Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet R)

theorem eLpNorm_cube_le_of_local_le {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] (Q : TriadicCube d) (k : ℕ)
    {f : Vec d → E} {g : Vec d → F} {p : ℝ≥0∞} {C : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpTop : p ≠ ⊤)
    (hf : AEStronglyMeasurable f (volume.restrict (openCubeSet Q)))
    (hg : AEStronglyMeasurable g (volume.restrict (openCubeSet Q)))
    (hlocal : ∀ R ∈ descendantsAtDepth Q k,
      eLpNorm f p (volume.restrict (openCubeSet R)) ≤
        C * eLpNorm g p (volume.restrict (openCubeSet R))) :
    eLpNorm f p (volume.restrict (openCubeSet Q)) ≤
      C * eLpNorm g p (volume.restrict (openCubeSet Q)) := by
  rw [volume_restrict_openCube_eq_sum_descendants Q k] at hf hg ⊢
  exact eLpNorm_finsetSum_measure_le _ _ hp0 hpTop hf hg hlocal

end CoarseDeGiorgi.Endpoint.Reconstruction
