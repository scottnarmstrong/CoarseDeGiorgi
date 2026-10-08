module

public import CoarseDeGiorgi.Weighted.SmoothSpace
public import CoarseDeGiorgi.Weighted.Identification

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

omit [NeZero d] in
/-- A smooth graph Cauchy sequence satisfies the Cauchy condition of the weighted completion. -/
theorem smoothGraph_cauchy (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {f : ℕ → smoothCoreSubmodule hV ha} (hc : CauchySeq (fun n => smoothGraphMap hV ha (f n))) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      ENNReal.ofReal ((volumeAverage V (fun x => (f n).val x - (f m).val x)) ^ 2) +
        weightedEnergy a V (fun x => smoothGrad (f n).val x - smoothGrad (f m).val x) <
        ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨N, fun m n hm hn => ?_⟩
  change ENNReal.ofReal ((volumeAverage V ((f n).val - (f m).val)) ^ 2) +
    weightedEnergy a V (smoothGrad (f n).val - smoothGrad (f m).val) < _
  rw [smoothGraph_distance]
  apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
  have hh := hN n hn m hm
  rw [dist_eq_norm] at hh
  nlinarith only [hh, norm_nonneg (smoothGraphMap hV ha (f n) - smoothGraphMap hV ha (f m)),
    Real.sq_sqrt hε.le]

omit [NeZero d] in
/-- Restricting global L¹ convergence gives the local integral convergence in the weighted graph. -/
theorem local_l1_of_global {f : ℕ → Vec d → ℝ} {u : Vec d → ℝ}
    (hf : ∀ n, IntegrableOn (f n) V) (hu : IntegrableOn u V)
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    {K : Set (Vec d)} (hK : K ⊆ V) :
    Tendsto (fun n => ∫⁻ x in K, ‖f n x - u x‖ₑ) atTop (𝓝 0) := by
  have htV : Tendsto (fun n => ∫⁻ x in V, ‖f n x - u x‖ₑ) atTop (𝓝 0) := by
    simpa only [eLpNorm_one_eq_lintegral_enorm ((hf _).sub hu).1, Pi.sub_apply] using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htV
    (fun _ => bot_le) (fun n => lintegral_mono_set hK)

/-- Limits of smooth graphs give the literal measurable value-gradient pairs of `MemH1a`. -/
theorem memH1a_of_smoothGraph_tendsto (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {f : ℕ → smoothCoreSubmodule hV.isOpen ha}
    {x : WeightedAmbient ha}
    (ht : Tendsto (fun n => smoothGraphMap hV.isOpen ha (f n)) atTop (𝓝 x)) :
    ∃ u : Vec d → ℝ,
      MemH1a a V u (gradientHilbertRep ha x.snd).field ∧
      volumeAverage V u = x.fst ∧ IntegrableOn u V ∧
        Tendsto (fun n => eLpNorm ((f n).val - u) 1 (volume.restrict V)) atTop (𝓝 0) := by
  have hc := smoothGraph_cauchy hV.isOpen ha ht.cauchySeq
  obtain ⟨u, hu, htu⟩ := exists_l1_limit_of_cauchy (fun n => (f n).property.2.1)
    (core_l1_cauchy hV hne ha (fun n => (f n).property) hc)
  have htG : Tendsto (fun n => (smoothEnergyField hV.isOpen ha (f n).property : GradientHilbert ha))
      atTop (𝓝 (gradientHilbertRep ha x.snd : GradientHilbert ha)) := by
    rw [gradientHilbertRep_coe]
    exact (WithLp.sndL 2 ℝ (ℝ) (GradientHilbert ha)).continuous.continuousAt.tendsto.comp ht
  have hE := GradientCore.tendsto_energy_of_coe ha htG
  refine ⟨u, ⟨hu.1, GradientCore.measurable ha _,
    fun n => (f n).val, fun n => (f n).property, hc,
    fun K _ hKV => local_l1_of_global (fun n => (f n).property.2.1) hu htu hKV, ?_⟩, ?_, hu, htu⟩
  · change Tendsto (fun n => weightedEnergy a V
      (smoothGrad (f n).val - (gradientHilbertRep ha x.snd).field)) atTop (𝓝 0)
    simpa only [smoothEnergyField_field] using hE
  · have hi := tendsto_integral_of_L1' u
      (Eventually.of_forall fun n => (f n).property.2.1) htu
    have hm : Tendsto (fun n => volumeAverage V (f n).val) atTop (𝓝 (volumeAverage V u)) := by
      exact hi.const_mul _
    have hx : Tendsto (fun n => volumeAverage V (f n).val) atTop (𝓝 x.fst) :=
      (WithLp.fstL 2 ℝ (ℝ) (GradientHilbert ha)).continuous.continuousAt.tendsto.comp ht
    exact tendsto_nhds_unique hm hx

/-- A weighted Sobolev gradient as an element of the shared energy core. -/
noncomputable def memH1aEnergyField (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G) : GradientCore ha :=
  ⟨G, hu.2.1, quadratic_integrable ha hu.2.1 (hu.energy_lt_top hV ha)⟩

omit [NeZero d] in
theorem memH1aEnergyField_field (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G) :
    (memH1aEnergyField hV ha hu).field = G := rfl

omit [NeZero d] in
/-- L¹ value convergence and energy convergence determine the ambient graph limit. -/
theorem smoothGraph_tendsto_of_l1_energy (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {f : ℕ → smoothCoreSubmodule hV ha} {u : Vec d → ℝ} {G : GradientCore ha}
    (hL : Tendsto (fun n => eLpNorm ((f n).val - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (smoothGrad (f n).val - G.field)) atTop (𝓝 0)) :
    Tendsto (fun n => smoothGraphMap hV ha (f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V u, (G : GradientHilbert ha)))) := by
  have htmean : Tendsto (fun n => volumeAverage V (f n).val) atTop (𝓝 (volumeAverage V u)) :=
    (tendsto_integral_of_L1' u (Eventually.of_forall fun n => (f n).property.2.1) hL).const_mul _
  have htgrad : Tendsto (fun n => (smoothEnergyField hV ha (f n).property : GradientHilbert ha))
      atTop (𝓝 (G : GradientHilbert ha)) := by
    apply GradientCore.tendsto_coe_of_energy ha
    simpa only [smoothEnergyField_field] using hE
  exact (WithLp.prod_continuous_toLp 2 ℝ (GradientHilbert ha)).continuousAt.tendsto.comp
    (htmean.prodMk_nhds htgrad)

omit [NeZero d] in
/-- A prescribed L¹ value and represented graph limit give a literal `MemH1a` pair. -/
theorem memH1a_of_graph_tendsto_and_l1 (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {f : ℕ → smoothCoreSubmodule hV ha} {u : Vec d → ℝ} {G : GradientCore ha}
    (hi : IntegrableOn u V)
    (hL : Tendsto (fun n => eLpNorm ((f n).val - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (ht : Tendsto (fun n => smoothGraphMap hV ha (f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V u, (G : GradientHilbert ha))))) :
    MemH1a a V u G.field := by
  have htG : Tendsto (fun n => (smoothEnergyField hV ha (f n).property : GradientHilbert ha))
      atTop (𝓝 (G : GradientHilbert ha)) :=
    (WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).continuous.continuousAt.tendsto.comp ht
  have hE := GradientCore.tendsto_energy_of_coe ha htG
  refine ⟨hi.1, GradientCore.measurable ha G, fun n => (f n).val,
    fun n => (f n).property, ?_, ?_, ?_⟩
  · exact smoothGraph_cauchy hV ha ht.cauchySeq
  · intro K _ hKV
    exact local_l1_of_global (fun n => (f n).property.2.1) hi hL hKV
  · change Tendsto (fun n => weightedEnergy a V (smoothGrad (f n).val - G.field)) atTop (𝓝 0)
    simpa only [smoothEnergyField_field] using hE

/-- Weighted Sobolev approximations converge in the shared graph carrier. -/
theorem MemH1a.smoothGraph_tendsto (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G) :
    ∃ f : ℕ → smoothCoreSubmodule hV.isOpen ha,
      Tendsto (fun n => smoothGraphMap hV.isOpen ha (f n)) atTop
        (𝓝 (WithLp.toLp 2 (volumeAverage V u,
          (memH1aEnergyField hV.isOpen ha hu : GradientHilbert ha)))) ∧
      Tendsto (fun n => eLpNorm ((f n).val - u) 1 (volume.restrict V)) atTop (𝓝 0) := by
  have hdata := hu
  obtain ⟨huM, hG, φ, hφ, hc, hlocal, henergy⟩ := hdata
  have htL := core_tendsto_l1 hV hne ha hφ hc huM hlocal
  let f : ℕ → smoothCoreSubmodule hV.isOpen ha := fun n => ⟨φ n, hφ n⟩
  have htmean : Tendsto (fun n => volumeAverage V (φ n)) atTop (𝓝 (volumeAverage V u)) :=
    (tendsto_integral_of_L1' u (Eventually.of_forall fun n => (hφ n).2.1) htL.2).const_mul _
  have htgrad : Tendsto (fun n => (smoothEnergyField hV.isOpen ha (hφ n) : GradientHilbert ha))
      atTop (𝓝 (memH1aEnergyField hV.isOpen ha hu : GradientHilbert ha)) := by
    apply GradientCore.tendsto_coe_of_energy ha
    exact henergy
  refine ⟨f, ?_, htL.2⟩
  exact (WithLp.prod_continuous_toLp 2 ℝ (GradientHilbert ha)).continuousAt.tendsto.comp
    (htmean.prodMk_nhds htgrad)

/-- Every `MemH1a` pair maps into the full weighted Hilbert graph. -/
theorem MemH1a.graph_mem (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G) :
    WithLp.toLp 2 (volumeAverage V u,
      (memH1aEnergyField hV.isOpen ha hu : GradientHilbert ha)) ∈
        weightedSubmodule hV.isOpen ha := by
  obtain ⟨f, ht, _⟩ := hu.smoothGraph_tendsto hV hne ha
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
    (Eventually.of_forall fun n => subset_closure ⟨f n, rfl⟩)

/-- Every element of the full Hilbert carrier represents a weighted Sobolev pair. -/
theorem weightedHilbert_exists_rep (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (x : WeightedHilbert hV.isOpen ha) :
    ∃ u : Vec d → ℝ, MemH1a a V u (gradientHilbertRep ha x.val.snd).field ∧
      volumeAverage V u = x.val.fst := by
  obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp x.property
  choose f hf using hy
  have htf : Tendsto (fun n => smoothGraphMap hV.isOpen ha (f n)) atTop (𝓝 x.val) := by
    simpa only [hf] using ht
  obtain ⟨u, hu, hm, _, _⟩ := memH1a_of_smoothGraph_tendsto hV hne ha htf
  exact ⟨u, hu, hm⟩



end CoarseDeGiorgi.Weighted
