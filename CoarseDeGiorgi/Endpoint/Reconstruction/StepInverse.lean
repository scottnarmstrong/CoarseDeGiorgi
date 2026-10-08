module

public import CoarseDeGiorgi.Endpoint.Reconstruction.Cancellation

/-! # Inverse bounds for fields constant on equal-volume cells -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

theorem eLpNorm_le_of_ae_scaled_bound {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} {r p : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hrp : r ≤ p)
    (hf : AEStronglyMeasurable f μ) (D : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ D * eLpNorm f (ENNReal.ofReal r) μ) :
    eLpNorm f (ENNReal.ofReal p) μ ≤
      D ^ (1 - r / p) * eLpNorm f (ENNReal.ofReal r) μ := by
  let N := eLpNorm f (ENNReal.ofReal r) μ
  have hpr : 0 ≤ p - r := sub_nonneg.mpr hrp
  have hpower : (1 - r / p) * p = p - r := by field_simp
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, hpower]
  have hnormp := eLpNorm_rpow_eq_lintegral_enorm
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hf
  have hnormr := eLpNorm_rpow_eq_lintegral_enorm
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top hf
  rw [ENNReal.toReal_ofReal hp.le] at hnormp
  rw [ENNReal.toReal_ofReal hr.le] at hnormr
  rw [hnormp]
  calc
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤ (D * N) ^ (p - r) * ∫⁻ x, ‖f x‖ₑ ^ r ∂μ := by
      rw [← lintegral_const_mul'' _ (hf.enorm.pow_const r)]
      apply lintegral_mono_ae
      filter_upwards [hbound] with x hx
      calc
        _ = ‖f x‖ₑ ^ (p - r) * ‖f x‖ₑ ^ r := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ hpr hr.le,
            show p - r + r = p by ring]
        _ ≤ _ := by gcongr
    _ = D ^ (p - r) * N ^ p := by
      rw [← hnormr, ENNReal.mul_rpow_of_nonneg _ _ hpr, mul_assoc,
        ← ENNReal.rpow_add_of_nonneg _ _ hpr hr.le, show p - r + r = p by ring]

theorem ae_enorm_le_of_constant_on_equal_cells {α E ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] (s : Finset ι)
    (μ : ι → Measure α) {f : α → E} {r : ℝ} (hr : 0 < r)
    (δ : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hvolume : ∀ i ∈ s, μ i Set.univ = δ)
    (hconstant : ∀ i ∈ s, ∃ c : E, f =ᵐ[μ i] fun _ => c) :
    ∀ᵐ x ∂(∑ i ∈ s, μ i),
      ‖f x‖ₑ ≤ δ ^ (-(1 / r)) * eLpNorm f (ENNReal.ofReal r) (∑ i ∈ s, μ i) := by
  rw [ae_finsetSum_measure_iff]
  intro i hi
  obtain ⟨c, hc⟩ := hconstant i hi
  have hlocal : ‖c‖ₑ * δ ^ (1 / r) ≤
      eLpNorm f (ENNReal.ofReal r) (∑ j ∈ s, μ j) := by
    calc
      _ = eLpNorm f (ENNReal.ofReal r) (μ i) := by
        rw [eLpNorm_congr_ae hc, eLpNorm_const' c
          (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal hr.le, hvolume i hi]
      _ ≤ _ := eLpNorm_mono_measure f
        (Finset.single_le_sum (fun _ _ => bot_le) hi)
  have hcancel : δ ^ (-(1 / r)) * δ ^ (1 / r) = 1 := by
    rw [← ENNReal.rpow_add _ _ hδ0 hδtop, neg_add_cancel, ENNReal.rpow_zero]
  have hglobal : ‖c‖ₑ ≤ δ ^ (-(1 / r)) *
      eLpNorm f (ENNReal.ofReal r) (∑ j ∈ s, μ j) := by
    have h : δ ^ (-(1 / r)) * (‖c‖ₑ * δ ^ (1 / r)) ≤
        δ ^ (-(1 / r)) * eLpNorm f (ENNReal.ofReal r) (∑ j ∈ s, μ j) := by
      gcongr
    calc
      _ = δ ^ (-(1 / r)) * (‖c‖ₑ * δ ^ (1 / r)) := by
        rw [mul_left_comm, hcancel, mul_one]
      _ ≤ _ := h
  filter_upwards [hc] with x hx
  simpa only [hx] using hglobal

theorem eLpNorm_le_of_constant_on_equal_cells {α E ι : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] (s : Finset ι)
    (μ : ι → Measure α) {f : α → E} {r p : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hrp : r ≤ p)
    (hf : AEStronglyMeasurable f (∑ i ∈ s, μ i))
    (δ : ℝ≥0∞) (hδ0 : δ ≠ 0) (hδtop : δ ≠ ⊤)
    (hvolume : ∀ i ∈ s, μ i Set.univ = δ)
    (hconstant : ∀ i ∈ s, ∃ c : E, f =ᵐ[μ i] fun _ => c) :
    eLpNorm f (ENNReal.ofReal p) (∑ i ∈ s, μ i) ≤
      δ ^ (1 / p - 1 / r) * eLpNorm f (ENNReal.ofReal r) (∑ i ∈ s, μ i) := by
  have hb := eLpNorm_le_of_ae_scaled_bound hr hp hrp hf
    (δ ^ (-(1 / r)))
    (ae_enorm_le_of_constant_on_equal_cells s μ hr δ hδ0 hδtop hvolume hconstant)
  rwa [← ENNReal.rpow_mul, show (-(1 / r)) * (1 - r / p) = 1 / p - 1 / r by
    field_simp; ring] at hb

theorem fineIncrement_constant_on_finest_cell {d : ℕ} (k : ℕ)
    (G : Vec d → Vec d) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (Homogenization.originCube d 0) (k + 1)) :
    ∃ c : Vec d, fineIncrement k G =ᵐ[volume.restrict (openCubeSet R)] fun _ => c := by
  obtain ⟨S, hS, hRS⟩ := mem_descendantsAtDepth_succ_iff.mp hR
  refine ⟨cubeAverageVec R G -
    cubeAverageVec S G, ?_⟩
  filter_upwards [(fineAverage_eq_cubeProjectionVec_ae (k + 1) G).restrict,
    (fineAverage_eq_cubeProjectionVec_ae k G).restrict,
    ae_restrict_mem (isOpen_openCubeSet R).measurableSet] with x hx1 hx0 hxR
  dsimp [fineIncrement]
  rw [hx1, hx0, Foundations.Reconstruction.cubeProjectionVec_eq_cubeAverageVec_of_mem G
    hR (openCubeSet_subset_cubeSet R hxR),
    Foundations.Reconstruction.cubeProjectionVec_eq_cubeAverageVec_of_mem G
      hS (cubeSet_subset_of_mem_childCubes hRS (openCubeSet_subset_cubeSet R hxR))]

theorem volume_unit_descendant_eq {d : ℕ} {R : TriadicCube d} {k : ℕ}
    (hR : R ∈ descendantsAtDepth (Homogenization.originCube d 0) k) :
    volume (openCubeSet R) = ENNReal.ofReal (((3 : ℝ) ^ (-(k : ℤ))) ^ d) := by
  rw [← ENNReal.ofReal_toReal (volume_openCubeSet_lt_top R).ne,
    volume_openCubeSet_toReal, cubeVolume, cubeScaleFactor_descendant hR,
    cubeScaleFactor_originCube, zpow_zero, one_mul]

theorem fineIncrement_inverse_bound {d : ℕ} (k : ℕ) (G : Vec d → Vec d)
    {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hrp : r ≤ p) :
    eLpNorm (fineIncrement k G) (ENNReal.ofReal p)
        (normalizedCubeMeasure (Homogenization.originCube d 0)) ≤
      (ENNReal.ofReal (((3 : ℝ) ^ (-((k + 1 : ℕ) : ℤ))) ^ d)) ^ (1 / p - 1 / r) *
        eLpNorm (fineIncrement k G) (ENNReal.ofReal r)
          (normalizedCubeMeasure (Homogenization.originCube d 0)) := by
  classical
  rw [normalizedCubeMeasure_unit_eq,
    volume_restrict_openCube_eq_sum_descendants (Homogenization.originCube d 0) (k + 1)]
  apply eLpNorm_le_of_constant_on_equal_cells _ _ hr hp hrp
  · rw [← volume_restrict_openCube_eq_sum_descendants]
    exact (memLp_fineIncrement k G (ENNReal.ofReal r)).aestronglyMeasurable.restrict
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · exact ENNReal.ofReal_ne_top
  · intro R hR
    rw [Measure.restrict_apply_univ]
    exact volume_unit_descendant_eq hR
  · exact fun R hR => fineIncrement_constant_on_finest_cell k G hR

end

end CoarseDeGiorgi.Endpoint.Reconstruction
