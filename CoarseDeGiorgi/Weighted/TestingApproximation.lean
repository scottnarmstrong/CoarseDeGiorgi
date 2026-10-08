module

public import CoarseDeGiorgi.Weighted.ZeroSpace
public import CoarseDeGiorgi.Weighted.Truncation.PositivePart

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Supported core limits in value L¹ and energy represent zero-boundary pairs. -/
theorem memH1a0_of_supported_tendsto (hV : IsOpenBoundedConvexDomain V)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ}
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) ∧ HasCompactSupport (f n) ∧
      tsupport (f n) ⊆ V)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : IntegrableOn u V volume)
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (smoothGrad (f n) - G)) atTop (𝓝 0)) :
    MemH1a0 a V u G := by
  have hcore := fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
  have hEG := energy_lt_top_of_tendsto ha
    (fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hcore n).1) hG
    (fun n => (hcore n).2.2) hE
  let H := energyField ha hG hEG
  let s : ℕ → smoothCoreSubmodule hV.isOpen ha := fun n => ⟨f n, hcore n⟩
  have hgraph := smoothGraph_tendsto_of_l1_energy hV.isOpen ha (f := s) (G := H) ht hE
  exact ⟨hu.1, hG, f, hf, smoothGraph_cauchy hV.isOpen ha (f := s) hgraph.cauchySeq,
    fun K _ hKV => local_l1_of_global (fun n => (hcore n).2.1) hu ht hKV, hE⟩

/-- The supported L¹-energy graph retains the value of the represented pair. -/
noncomputable def supportedL1Graph (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    (f : supportedCoreSubmodule V) : Lp ℝ 1 (volume.restrict V) × GradientHilbert ha :=
  coreL1Graph hV ha (supportedToSmooth hV ha f)

/-- The zero-boundary completion is the closed supported L¹-energy graph. -/
theorem memH1a0_iff_mem_closure [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IntegrableOn u V volume) (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) :
    MemH1a0 a V u G ↔
      ((memLp_one_iff_integrable.mpr hu).toLp u,
        (energyField ha hG hEG : GradientHilbert ha)) ∈
          closure (Set.range (supportedL1Graph hV.isOpen ha)) := by
  let H := energyField ha hG hEG
  constructor
  · intro h
    obtain ⟨_, _, f, hf, hc, hloc, hE⟩ := h
    have hcore := fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
    have hL := (core_tendsto_l1 hV hne ha hcore hc hu.1 hloc).2
    have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f
      (fun n => memLp_one_iff_integrable.mpr (hcore n).2.1) u
      (memLp_one_iff_integrable.mpr hu)).mpr hL
    have hg : Tendsto
        (fun n => (smoothEnergyField hV.isOpen ha (hcore n) : GradientHilbert ha))
        atTop (𝓝 (H : GradientHilbert ha)) := GradientCore.tendsto_coe_of_energy ha
          (F := fun n => smoothEnergyField hV.isOpen ha (hcore n)) (G := H) hE
    exact isClosed_closure.mem_of_tendsto (hv.prodMk_nhds hg)
      (Eventually.of_forall fun n => subset_closure ⟨⟨f n, hf n⟩, rfl⟩)
  · intro h
    obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp h
    choose f hf using hz
    have htf : Tendsto (fun n => supportedL1Graph hV.isOpen ha (f n)) atTop
        (𝓝 ((memLp_one_iff_integrable.mpr hu).toLp u, (H : GradientHilbert ha))) := by
      simpa only [hf] using ht
    have hcore := fun n => isSmoothCore_of_supported ha (f n).property.1 (f n).property.2.1
    have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (f n).val)
      (fun n => memLp_one_iff_integrable.mpr (hcore n).2.1) u
      (memLp_one_iff_integrable.mpr hu)).mp (continuous_fst.continuousAt.tendsto.comp htf)
    have hg : Tendsto
        (fun n => (smoothEnergyField hV.isOpen ha (hcore n) : GradientHilbert ha))
        atTop (𝓝 (H : GradientHilbert ha)) := continuous_snd.continuousAt.tendsto.comp htf
    exact memH1a0_of_supported_tendsto hV ha (fun n => (f n).property) hu hG hv
      (GradientCore.tendsto_energy_of_coe ha
        (F := fun n => smoothEnergyField hV.isOpen ha (hcore n)) (G := H) hg)

/-- Zero-boundary pairs are closed under value L¹ and weighted gradient convergence. -/
theorem memH1a0_of_tendsto [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ} {F : ℕ → Vec d → Vec d}
    (hf : ∀ n, MemH1a0 a V (f n) (F n))
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : IntegrableOn u V volume)
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0)) :
    MemH1a0 a V u G := by
  have hi := fun n => (memH1a_memW11 hV hne ha ((hf n).memH1a ha)).1
  have hEF := fun n => MemH1a.energy_lt_top hV.isOpen ha ((hf n).memH1a ha)
  have hEG := energy_lt_top_of_tendsto ha (fun n => (hf n).2.1) hG hEF hE
  let H := energyField ha hG hEG
  let D : ℕ → GradientCore ha := fun n => memH1aEnergyField hV.isOpen ha ((hf n).memH1a ha)
  have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f
    (fun n => memLp_one_iff_integrable.mpr (hi n)) u
    (memLp_one_iff_integrable.mpr hu)).mpr ht
  have hg : Tendsto (fun n => (D n : GradientHilbert ha)) atTop
      (𝓝 (H : GradientHilbert ha)) := GradientCore.tendsto_coe_of_energy ha (F := D) (G := H) hE
  apply (memH1a0_iff_mem_closure hV hne ha hu hG hEG).mpr
  apply isClosed_closure.mem_of_tendsto (hv.prodMk_nhds hg)
  exact Eventually.of_forall fun n =>
    (memH1a0_iff_mem_closure hV hne ha (hi n) (hf n).2.1 (hEF n)).mp (hf n)

/-- Smooth compositions fixing zero have supported smooth approximations. -/
theorem MemH1a0.comp_approximation [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a0 a V u G)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hzero : Φ 0 = 0)
    {L : ℝ≥0} (hbound : ∀ t, |deriv Φ t| ≤ L) :
    ∃ f : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ V) ∧
      (∀ n x, ∃ t : ℝ, f n x = Φ t) ∧
      Tendsto (fun n => eLpNorm (f n - Φ ∘ u) 1 (volume.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun n => weightedEnergy a V
        (smoothGrad (f n) - fun x => deriv Φ (u x) • G x)) atTop (𝓝 0) := by
  have hw := hu.memH1a ha
  have hEG := MemH1a.energy_lt_top hV.isOpen ha hw
  obtain ⟨f, htf, hL⟩ := hu.supportedGraph_tendsto hV hne ha
  have hcore := fun n => isSmoothCore_of_supported ha (f n).property.1 (f n).property.2.1
  have hE : Tendsto (fun n => weightedEnergy a V (smoothGrad (f n).val - G))
      atTop (𝓝 0) := by
    exact GradientCore.tendsto_energy_of_coe ha
      (F := fun n => smoothEnergyField hV.isOpen ha (hcore n))
      (G := memH1aEnergyField hV.isOpen ha hw)
      ((WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).continuous.continuousAt.tendsto.comp htf)
  have hl : LipschitzWith L Φ := lipschitzWith_of_nnnorm_deriv_le (C := L)
    (hΦ.differentiable (by simp)) (fun t => NNReal.coe_le_coe.mp
      (by simpa only [coe_nnnorm, Real.norm_eq_abs] using hbound t))
  refine ⟨fun n => Φ ∘ (f n).val, (fun n => ⟨hΦ.comp (f n).property.1,
    (f n).property.2.1.comp_left hzero,
    (tsupport_comp_subset hzero (f n).val).trans (f n).property.2.2⟩),
    (fun n x => ⟨(f n).val x, rfl⟩),
    tendsto_l1_lipschitz_comp (fun n => (hcore n).2.1.1) hu.1 hL hl, ?_⟩
  have htE := tendsto_energy_continuous_factor ha
    (f := fun n => (f n).val) (F := fun n => smoothGrad (f n).val)
    (u := u) (G := G) (b := deriv Φ)
    (fun n => (hcore n).2.1.1) hu.1
    (fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hcore n).1) hu.2.1 hEG
    hL hE (hΦ.continuous_deriv (by simp)) hbound
  convert htE using 1
  funext n
  exact energy_congr_ae ((smoothGrad_comp_ae hV.isOpen (hcore n).1 hΦ).sub EventuallyEq.rfl)


end CoarseDeGiorgi.Weighted
