import CoarseDeGiorgi.Endpoint.Reconstruction.BlockContinuity
import CoarseDeGiorgi.Weighted.ZeroSpace

/-! # Smooth approximation with convergent literal energies -/
namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section

theorem energy_root_eq_norm {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (ha : IsWeightedCoeffOn U a) (F : Weighted.GradientCore ha) :
    (weightedEnergy a U F.field) ^ (1 / 2 : ℝ) = ENNReal.ofReal ‖F‖ := by
  change (Weighted.weightedEnergy a U F.field) ^ (1 / 2 : ℝ) = _
  rw [Weighted.GradientCore.energy_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem exists_smooth_energy_approximation {d : ℕ} [NeZero d]
    (a : CoeffField d) (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d} (hv : MemH1a0 a (CoarseDeGiorgi.originCube 1) v G) :
    ∃ f : ℕ → Weighted.supportedCoreSubmodule (CoarseDeGiorgi.originCube (d := d) 1),
      Tendsto (fun j => eLpNorm ((f j).val - v) 1 (volume.restrict (CoarseDeGiorgi.originCube 1))) atTop (𝓝 0) ∧
      Tendsto (fun j => weightedEnergy a (CoarseDeGiorgi.originCube 1) (smoothGrad (f j).val - G)) atTop (𝓝 0) ∧
      Tendsto (fun j => (weightedEnergy a (CoarseDeGiorgi.originCube 1) (smoothGrad (f j).val)) ^ (1 / 2 : ℝ))
        atTop (𝓝 ((weightedEnergy a (CoarseDeGiorgi.originCube 1) G) ^ (1 / 2 : ℝ))) := by
  have hU := LowerFractional.lower_unitCube_domain (d := d)
  have hne := LowerFractional.lower_unitCube_nonempty (d := d)
  obtain ⟨f, ht, hL⟩ := Weighted.MemH1a0.supportedGraph_tendsto hU hne ha hv
  let F (j : ℕ) := Weighted.smoothEnergyField hU.isOpen ha
    (Weighted.isSmoothCore_of_supported ha (f j).property.1 (f j).property.2.1)
  let H := Weighted.memH1aEnergyField hU.isOpen ha (Weighted.MemH1a0.memH1a ha hv)
  have htF : Tendsto (fun j => (F j : Weighted.GradientHilbert ha)) atTop (𝓝 (H : Weighted.GradientHilbert ha)) :=
    (WithLp.sndL 2 ℝ ℝ (Weighted.GradientHilbert ha)).continuous.continuousAt.tendsto.comp ht
  have he := Weighted.GradientCore.tendsto_energy_of_coe ha htF
  have hroot := ENNReal.tendsto_ofReal htF.norm
  simp only [UniformSpace.Completion.norm_coe] at hroot
  refine ⟨f, hL, he, ?_⟩
  simpa only [← energy_root_eq_norm ha, F, H, Weighted.smoothEnergyField_field,
    Weighted.memH1aEnergyField_field, Weighted.smoothGrad] using hroot

end
end CoarseDeGiorgi.Endpoint.Reconstruction
