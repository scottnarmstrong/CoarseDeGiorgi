import CoarseDeGiorgi.Selection.SourceTraces
import CoarseDeGiorgi.Weighted.TestingNonnegative

namespace CoarseDeGiorgi.Selection
open Homogenization MeasureTheory Filter Topology CoarseDeGiorgi.Weighted
open scoped ENNReal NNReal
noncomputable section
variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- Nonnegative smooth approximation for the full weighted space `MemH1a`,
proved by positive scalar composition and closure of the value/energy graph. -/
theorem source_nonnegative_approximation (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G) (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x) :
    ∃ f : ℕ → Vec d → ℝ,
      (∀ n, IsSmoothCore a V (f n) ∧ ∀ x, 0 ≤ f n x) ∧
      Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun n => weightedEnergy a V (smoothGrad (f n) - G)) atTop (𝓝 0) := by
  let S := {f : smoothCoreSubmodule hV.isOpen ha | ∀ x, 0 ≤ f.val x}
  let μ := volume.restrict V
  have hw := hu
  have hi := (memH1a_memW11 hV hne ha hw).1
  let H := memH1aEnergyField hV.isOpen ha hw
  let target : Lp ℝ 1 μ × GradientHilbert ha :=
    ((memLp_one_iff_integrable.mpr hi).toLp u, (H : GradientHilbert ha))
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδpos : ∀ n, 0 < δ n := by intro n; positivity
  let v : ℕ → Vec d → ℝ := fun n => GApprox 0 (δ n) ∘ u
  let D : ℕ → Vec d → Vec d := fun n x => gStep 0 (δ n) (u x) • G x
  have hv (n : ℕ) : CoarseDeGiorgi.MemH1a a V (v n) (D n) := by
    simpa only [deriv_GApprox] using MemH1a.comp hV hne ha hw
      (GApprox_contDiff_top 0 (δ n)) (L := 1) (abs_deriv_GApprox_le 0 (δ n))
  let J : ℕ → GradientCore ha := fun n => memH1aEnergyField hV.isOpen ha (hv n)
  have hvi := fun n => (memH1a_memW11 hV hne ha (hv n)).1
  have hmem (n : ℕ) : ((memLp_one_iff_integrable.mpr (hvi n)).toLp (v n),
      (J n : GradientHilbert ha)) ∈ closure (coreL1Graph hV.isOpen ha '' S) := by
    obtain ⟨uM, hG, f₀, hf₀, hc, hloc, hE₀⟩ := hu
    have hL₀ := (core_tendsto_l1 hV hne ha hf₀ hc uM hloc).2
    let Φ := GApprox 0 (δ n)
    let f : ℕ → Vec d → ℝ := fun k => Φ ∘ f₀ k
    have hf (k : ℕ) : IsSmoothCore a V (f k) :=
      IsSmoothCore.comp hV ha (hf₀ k) (GApprox_contDiff_top 0 (δ n))
        (L := 1) (abs_deriv_GApprox_le 0 (δ n))
    have hl : LipschitzWith 1 Φ := lipschitzWith_of_nnnorm_deriv_le
      ((GApprox_contDiff_top 0 (δ n)).differentiable (by simp))
      (fun t => NNReal.coe_le_coe.mp (by
        change |deriv (GApprox 0 (δ n)) t| ≤ 1
        exact abs_deriv_GApprox_le 0 (δ n) t))
    have hL := tendsto_l1_lipschitz_comp (fun k => (hf₀ k).2.1.1) uM hL₀ hl
    have hE : Tendsto (fun k => weightedEnergy a V (smoothGrad (f k) - D n)) atTop (𝓝 0) := by
      have htE := tendsto_energy_continuous_factor ha (fun k => (hf₀ k).2.1.1) uM
        (fun k => smoothGrad_aestronglyMeasurable hV.isOpen (hf₀ k).1) hG
        (MemH1a.energy_lt_top hV.isOpen ha hw) hL₀ hE₀
        ((GApprox_contDiff_top 0 (δ n)).continuous_deriv (by simp))
        (abs_deriv_GApprox_le 0 (δ n))
      convert htE using 1
      funext k
      simpa only [D, deriv_GApprox] using energy_congr_ae
        ((smoothGrad_comp_ae hV.isOpen (hf₀ k).1
          (GApprox_contDiff_top 0 (δ n))).sub EventuallyEq.rfl)
    have hg : Tendsto (fun k =>
        (smoothEnergyField hV.isOpen ha (hf k) :
          GradientHilbert ha)) atTop (𝓝 (J n : GradientHilbert ha)) :=
      GradientCore.tendsto_coe_of_energy ha
        (F := fun k => smoothEnergyField hV.isOpen ha
          (hf k)) (G := J n)
        hE
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f
      (fun k => memLp_one_iff_integrable.mpr
        (hf k).2.1) (v n)
      (memLp_one_iff_integrable.mpr (hvi n))).mpr hL
    apply isClosed_closure.mem_of_tendsto (ht.prodMk_nhds hg)
    apply Eventually.of_forall
    intro k
    apply subset_closure
    refine ⟨⟨f k, hf k⟩, ?_, rfl⟩
    intro x
    change 0 ≤ f k x
    exact GApprox_nonneg (hδpos n) (f₀ k x)
  obtain ⟨hL, hE⟩ := nonnegative_GApprox_tendsto hV hne ha hw hnonneg
  have htarget : target ∈ closure (coreL1Graph hV.isOpen ha '' S) := by
    have hvlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v
      (fun n => memLp_one_iff_integrable.mpr (hvi n)) u
      (memLp_one_iff_integrable.mpr hi)).mpr hL
    have hglim := GradientCore.tendsto_coe_of_energy ha (F := J) (G := H) hE
    exact isClosed_closure.mem_of_tendsto (hvlim.prodMk_nhds hglim)
      (Eventually.of_forall hmem)
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp htarget
  choose f hf heq using hz
  have htf : Tendsto (fun n => coreL1Graph hV.isOpen ha (f n)) atTop (𝓝 target) := by
    simpa only [heq] using ht
  have hvlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (f n).val)
    (fun n => memLp_one_iff_integrable.mpr
      (f n).property.2.1) u
    (memLp_one_iff_integrable.mpr hi)).mp (continuous_fst.continuousAt.tendsto.comp htf)
  have hglim : Tendsto (fun n =>
      (smoothEnergyField hV.isOpen ha
        (f n).property : GradientHilbert ha))
      atTop (𝓝 (H : GradientHilbert ha)) := continuous_snd.continuousAt.tendsto.comp htf
  exact ⟨fun n => (f n).val, fun n => ⟨(f n).property, hf n⟩, hvlim,
    GradientCore.tendsto_energy_of_coe ha
      (F := fun n => smoothEnergyField hV.isOpen ha
        (f n).property) (G := H) hglim⟩

end
end CoarseDeGiorgi.Selection
