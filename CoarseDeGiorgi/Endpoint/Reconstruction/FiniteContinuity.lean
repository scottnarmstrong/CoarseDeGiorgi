import CoarseDeGiorgi.Endpoint.Reconstruction.BlockContinuity

/-! # Continuity of fixed finite block sums -/
namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section

theorem tendsto_eLpNorm_finset_sum_sub {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p) (s : Finset ι)
    (f : ℕ → ι → α → ℝ) (g : ι → α → ℝ)
    (ht : ∀ k ∈ s, Tendsto (fun j => eLpNorm (f j k - g k) p μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm ((∑ k ∈ s, f j k) - ∑ k ∈ s, g k) p μ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun j => ∑ k ∈ s, eLpNorm (f j k - g k) p μ) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum s ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le) ?_
  intro j
  dsimp only
  rw [← Finset.sum_sub_distrib]
  exact eLpNorm_sum_le hp

theorem unit_l1_le_lp {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (CoarseDeGiorgi.originCube 1))) :
    eLpNorm f 1 (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
      eLpNorm f p (volume.restrict (CoarseDeGiorgi.originCube 1)) := by
  have hmass : (volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)) Set.univ = 1 := by
    rw [originCube_one_eq_openCubeSet, ← normalizedCubeMeasure_unit_eq]
    exact normalizedCubeMeasure_apply_univ _
  simpa only [hmass, ENNReal.one_rpow, mul_one] using
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf

end
end CoarseDeGiorgi.Endpoint.Reconstruction
