module

public import CoarseDeGiorgi.Endpoint.Reconstruction.ProjectionAlgebra
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Homogenization.Sobolev.FiniteLpCoordinate

/-! # L2 convergence of triadic projections for bounded input -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

theorem norm_cubeProjection_le_of_bound {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ x ∈ cubeSet Q, ‖f x‖ ≤ B) (n : ℕ) :
    ∀ x ∈ cubeSet Q, ‖cubeProjection Q n f x‖ ≤ B := by
  intro x hx
  obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet n hx
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  have hRbound : ∀ᵐ y ∂normalizedCubeMeasure R, ‖f y‖ ≤ B := by
    apply Measure.ae_smul_measure
    exact (ae_restrict_mem (measurableSet_cubeSet R)).mono fun y hy =>
      hbound y (cubeSet_subset_of_mem_descendantsAtDepth hR hy)
  have h := norm_integral_le_of_norm_le_const hRbound
  simpa only [Measure.real, normalizedCubeMeasure_apply_univ, ENNReal.toReal_one, mul_one] using h

theorem tendsto_eLpNorm_cubeProjection_sub_two_of_bound {d : ℕ}
    (Q : TriadicCube d) (f : Vec d → ℝ) (hf : IntegrableOn f (cubeSet Q))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x ∈ cubeSet Q, ‖f x‖ ≤ B) :
    Tendsto (fun n => eLpNorm (fun x => cubeProjection Q n f x - f x) 2
      (volume.restrict (cubeSet Q))) atTop (𝓝 0) := by
  let μ := volume.restrict (cubeSet Q)
  let : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using volume_cubeSet_lt_top Q⟩
  let E : ℕ → Vec d → ℝ := fun n x => cubeProjection Q n f x - f x
  have hmeas (n : ℕ) : AEStronglyMeasurable (E n) μ :=
    (integrableOn_cubeProjection_of_integrableOn Q n f).aestronglyMeasurable.sub hf.aestronglyMeasurable
  have hEbound (n : ℕ) : ∀ᵐ x ∂μ, ‖E n x‖ ≤ 2 * B := by
    filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
    exact (norm_sub_le _ _).trans ((add_le_add
      (norm_cubeProjection_le_of_bound Q f hB hbound n x hx) (hbound x hx)).trans_eq (two_mul B).symm)
  have hE2 (n : ℕ) : MemLp (E n) 2 μ := MemLp.of_bound (hmeas n) (2 * B) (hEbound n)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => E n x) atTop (𝓝 0) := by
    exact (ae_tendsto_cubeProjection_of_integrableOn Q f hf).mono fun x hx =>
      by simpa only [E, sub_self] using hx.sub_const (f x)
  have hInt : Tendsto (fun n => ∫ x, ‖E n x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_filter_of_norm_le_const
      (μ := μ) (F := fun n x => ‖E n x‖ ^ 2) (f := fun _ => (0 : ℝ))
      (Eventually.of_forall fun n => (hmeas n).norm.fun_pow 2)
      ⟨(2 * B) ^ 2, Eventually.of_forall fun n => (hEbound n).mono fun x hx => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hx 2⟩
      (hlim.mono fun x hx => by simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hx.norm.pow 2)
    simpa only [integral_zero] using hh
  have heq (n : ℕ) : eLpNorm (E n) 2 μ = ENNReal.ofReal ((∫ x, ‖E n x‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
    rw [(hE2 n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  simp_rw [show (fun n => eLpNorm (fun x => cubeProjection Q n f x - f x) 2
      (volume.restrict (cubeSet Q))) = (fun n => eLpNorm (E n) 2 μ) from rfl, heq]
  have hs := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.tendsto.comp hInt
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), ENNReal.ofReal_zero] using hh

theorem tendsto_eLpNorm_fineAverage_sub_hilbert_two_of_bound {d : ℕ}
    (G : Vec d → Vec d) (hG : IntegrableOn G (CoarseDeGiorgi.originCube 1))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x ∈ cubeSet (Homogenization.originCube d 0), ‖G x‖ ≤ B) :
    Tendsto (fun n => eLpNorm (fun x => HilbertVec.ofVec (fineAverage n G x - G x)) 2
      (volume.restrict (CoarseDeGiorgi.originCube 1))) atTop (𝓝 0) := by
  let Q := Homogenization.originCube d 0
  let μ := volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)
  have hGQ := integrableOn_unit_cubeSet hG
  have hcoord (i : Fin d) : Tendsto
      (fun n => eLpNorm (fun x => fineAverage n G x i - G x i) 2 μ) atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_cubeProjection_sub_two_of_bound Q (fun x => G x i)
      (hGQ.eval i) hB (fun x hx => (norm_le_pi_norm (G x) i).trans (hbound x hx))
    have hμ : volume.restrict (cubeSet Q) = μ := by
      rw [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet Q)]
      dsimp [μ, Q]
      rw [originCube_one_eq_openCubeSet]
    rw [hμ] at h
    apply h.congr'
    exact Eventually.of_forall fun n => eLpNorm_congr_ae (by
      filter_upwards [(fineAverage_eq_cubeProjectionVec_ae n G).restrict] with x hx
      change cubeProjection Q n (fun y => G y i) x - G x i = fineAverage n G x i - G x i
      rw [hx]
      rfl)
  have hsum : Tendsto (fun n => ∑ i : Fin d,
      eLpNorm (fun x => fineAverage n G x i - G x i) 2 μ) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  have hD := ENNReal.Tendsto.const_mul hsum (Or.inr (by exact enorm_ne_top : ‖(d : ℝ)‖ₑ ≠ ⊤))
  simp only [mul_zero] at hD
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hD (fun _ => bot_le)
  intro n
  exact euclidean_eLpNorm_le_dimension_mul_sum_coordinates μ ⟨2, by norm_num, by norm_num⟩
    (fun x => fineAverage n G x - G x) (fun i => by
      exact (continuous_apply i).comp_aestronglyMeasurable
        ((memLp_fineAverage n G 2).aestronglyMeasurable.restrict.sub hG.aestronglyMeasurable))

end

end CoarseDeGiorgi.Endpoint.Reconstruction
