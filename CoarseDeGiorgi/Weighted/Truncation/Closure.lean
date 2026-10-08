import CoarseDeGiorgi.Weighted.Truncation.Energy

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

omit [NeZero d] in
/-- Smooth core convergence in value L¹ and weighted energy gives `MemH1a` membership. -/
theorem memH1a_of_core_tendsto (hV : IsOpenBoundedConvexDomain V)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ}
    (hf : ∀ n, CoarseDeGiorgi.IsSmoothCore a V (f n))
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : IntegrableOn u V volume)
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (smoothGrad (f n) - G)) atTop (𝓝 0)) :
    CoarseDeGiorgi.MemH1a a V u G := by
  have hEG := energy_lt_top_of_tendsto ha
    (fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hf n).1) hG
    (fun n => (hf n).2.2) hE
  let H : GradientCore ha := ⟨G, hG, quadratic_integrable ha hG hEG⟩
  let F : ℕ → smoothCoreSubmodule hV.isOpen ha := fun n => ⟨f n, hf n⟩
  have hmean : Tendsto (fun n => volumeAverage V (f n)) atTop
      (𝓝 (volumeAverage V u)) :=
    (tendsto_integral_of_L1' u (Eventually.of_forall fun n => (hf n).2.1) ht).const_mul _
  have hgrad : Tendsto
      (fun n => (smoothEnergyField hV.isOpen ha (hf n) : GradientHilbert ha))
      atTop (𝓝 (H : GradientHilbert ha)) :=
    GradientCore.tendsto_coe_of_energy ha
      (F := fun n => smoothEnergyField hV.isOpen ha (hf n)) (G := H) hE
  have hgraph : Tendsto (fun n => smoothGraphMap hV.isOpen ha (F n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V u, (H : GradientHilbert ha)))) :=
    (WithLp.prod_continuous_toLp 2 ℝ (GradientHilbert ha)).continuousAt.tendsto.comp
      (hmean.prodMk_nhds hgrad)
  exact ⟨hu.1, hG, f, hf, smoothGraph_cauchy hV.isOpen ha (f := F) hgraph.cauchySeq,
    fun K _ hKV => local_l1_of_global (fun n => (hf n).2.1) hu ht hKV, hE⟩

omit [NeZero d] in
/-- Membership is unchanged by a.e. changes of the represented pair. -/
theorem MemH1a.congr_ae {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G)
    (huv : u =ᵐ[volume.restrict V] v) (hGH : G =ᵐ[volume.restrict V] H) :
    CoarseDeGiorgi.MemH1a a V v H := by
  obtain ⟨huM, hGM, f, hf, hc, ht, hE⟩ := hu
  refine ⟨huM.congr huv, hGM.congr hGH, f, hf, hc, ?_, ?_⟩
  · intro K hK hKV
    have heq := ae_mono (Measure.restrict_mono hKV le_rfl) huv
    convert ht K hK hKV using 1
    funext n
    apply lintegral_congr_ae
    filter_upwards [heq] with x hx
    rw [hx]
  · convert hE using 1
    funext n
    exact energy_congr_ae (EventuallyEq.rfl.sub hGH.symm)

/-- Smooth graphs with the value retained in L¹, for literal-pair closedness. -/
noncomputable def coreL1Graph (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    (f : smoothCoreSubmodule hV ha) :
    Lp ℝ 1 (volume.restrict V) × GradientHilbert ha :=
  ((memLp_one_iff_integrable.mpr f.property.2.1).toLp f.val,
    (smoothEnergyField hV ha f.property : GradientHilbert ha))

/-- A measurable finite-energy field in the raw energy space. -/
noncomputable def energyField (ha : IsWeightedCoeffOn V a) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) : GradientCore ha :=
  ⟨G, hG, quadratic_integrable ha hG hEG⟩

/-- `MemH1a` membership is precisely membership in the closed L¹-energy graph. -/
theorem memH1a_iff_mem_closure (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : IntegrableOn u V volume) (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) :
    CoarseDeGiorgi.MemH1a a V u G ↔
      ((memLp_one_iff_integrable.mpr hu).toLp u,
        (energyField ha hG hEG : GradientHilbert ha))
      ∈ closure (Set.range (coreL1Graph hV.isOpen ha)) := by
  let H : GradientCore ha := energyField ha hG hEG
  constructor
  · intro h
    obtain ⟨huM, _, f, hf, hc, hloc, hE⟩ := h
    have hL := (core_tendsto_l1 hV hne ha hf hc huM hloc).2
    have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f
      (fun n => memLp_one_iff_integrable.mpr (hf n).2.1) u
      (memLp_one_iff_integrable.mpr hu)).mpr hL
    have hg : Tendsto
        (fun n => (smoothEnergyField hV.isOpen ha (hf n) : GradientHilbert ha))
        atTop (𝓝 (H : GradientHilbert ha)) := GradientCore.tendsto_coe_of_energy ha
          (F := fun n => smoothEnergyField hV.isOpen ha (hf n)) (G := H) hE
    exact isClosed_closure.mem_of_tendsto (hv.prodMk_nhds hg)
      (Eventually.of_forall fun n => subset_closure ⟨⟨f n, hf n⟩, rfl⟩)
  · intro h
    obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp h
    choose f hf using hz
    have htf : Tendsto (fun n => coreL1Graph hV.isOpen ha (f n)) atTop
        (𝓝 ((memLp_one_iff_integrable.mpr hu).toLp u, (H : GradientHilbert ha))) := by
      simpa only [hf] using ht
    have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (f n).val)
      (fun n => memLp_one_iff_integrable.mpr (f n).property.2.1) u
      (memLp_one_iff_integrable.mpr hu)).mp (continuous_fst.continuousAt.tendsto.comp htf)
    have hg : Tendsto
        (fun n => (smoothEnergyField hV.isOpen ha (f n).property : GradientHilbert ha))
        atTop (𝓝 (H : GradientHilbert ha)) := continuous_snd.continuousAt.tendsto.comp htf
    exact memH1a_of_core_tendsto hV ha (fun n => (f n).property) hu hG hv
      (GradientCore.tendsto_energy_of_coe ha
        (F := fun n => smoothEnergyField hV.isOpen ha (f n).property) (G := H) hg)

/-- Closedness of the weighted completion under value L¹ and weighted gradient convergence. -/
theorem memH1a_of_tendsto (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → Vec d → ℝ} {F : ℕ → Vec d → Vec d}
    (hf : ∀ n, CoarseDeGiorgi.MemH1a a V (f n) (F n))
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : IntegrableOn u V volume)
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0)) :
    CoarseDeGiorgi.MemH1a a V u G := by
  have hi := fun n => (memH1a_memW11 hV hne ha (hf n)).1
  have hEF := fun n => MemH1a.energy_lt_top hV.isOpen ha (hf n)
  have hEG := energy_lt_top_of_tendsto ha (fun n => (hf n).2.1) hG hEF hE
  let H : GradientCore ha := energyField ha hG hEG
  let D : ℕ → GradientCore ha := fun n => memH1aEnergyField hV.isOpen ha (hf n)
  have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f
    (fun n => memLp_one_iff_integrable.mpr (hi n)) u
    (memLp_one_iff_integrable.mpr hu)).mpr ht
  have hg : Tendsto (fun n => (D n : GradientHilbert ha)) atTop
      (𝓝 (H : GradientHilbert ha)) := GradientCore.tendsto_coe_of_energy ha (F := D) (G := H) hE
  apply (memH1a_iff_mem_closure hV hne ha hu hG hEG).mpr
  apply isClosed_closure.mem_of_tendsto (hv.prodMk_nhds hg)
  exact Eventually.of_forall fun n =>
    (memH1a_iff_mem_closure hV hne ha (hi n) (hf n).2.1 (hEF n)).mp (hf n)

end CoarseDeGiorgi.Weighted
