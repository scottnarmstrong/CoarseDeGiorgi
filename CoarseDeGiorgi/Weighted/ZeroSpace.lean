module

public import CoarseDeGiorgi.Weighted.GraphRepresentation
public import CoarseDeGiorgi.Weighted.ZeroBoundary
public import Mathlib.Analysis.Normed.Operator.Banach

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The source's globally smooth, compactly supported boundary core. -/
noncomputable abbrev supportedCoreSubmodule (V : Set (Vec d)) :
    Submodule ℝ (Vec d → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V}
  zero_mem' := by
    refine ⟨contDiff_const, ?_, ?_⟩
    · exact HasCompactSupport.of_support_subset_isCompact isCompact_empty (by simp)
    · simp
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
      (tsupport_add f g).trans (Set.union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro c f hf
    exact ⟨hf.1.const_smul c, hf.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => c) f).trans hf.2.2⟩

/-- Inclusion of the supported core into the smooth core. -/
noncomputable def supportedToSmooth (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    supportedCoreSubmodule V →ₗ[ℝ] smoothCoreSubmodule hV ha where
  toFun f := ⟨f.val, isSmoothCore_of_supported ha f.property.1 f.property.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def supportedGraphMap (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    supportedCoreSubmodule V →ₗ[ℝ] WeightedAmbient ha :=
  (smoothGraphMap hV ha).comp (supportedToSmooth hV ha)

/-- The closed supported graph before restricting to its gradient image. -/
noncomputable abbrev zeroGraphSubmodule (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    Submodule ℝ (WeightedAmbient ha) := (supportedGraphMap hV ha).range.topologicalClosure

instance zeroGraph_complete (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    CompleteSpace (zeroGraphSubmodule hV ha) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Supported smooth graph limits represent the zero-boundary completion. -/
theorem memH1a0_of_smoothGraph_tendsto [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {f : ℕ → smoothCoreSubmodule hV.isOpen ha} {x : WeightedAmbient ha}
    (hs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n).val ∧ HasCompactSupport (f n).val ∧
      tsupport (f n).val ⊆ V)
    (ht : Tendsto (fun n => smoothGraphMap hV.isOpen ha (f n)) atTop (𝓝 x)) :
    ∃ u : Vec d → ℝ, MemH1a0 a V u (gradientHilbertRep ha x.snd).field ∧
      volumeAverage V u = x.fst := by
  obtain ⟨u, hu, hm, hi, htu⟩ := memH1a_of_smoothGraph_tendsto hV hne ha ht
  have htc : Tendsto (fun n => (smoothEnergyField hV.isOpen ha (f n).property : GradientHilbert ha))
      atTop (𝓝 (gradientHilbertRep ha x.snd : GradientHilbert ha)) := by
    rw [gradientHilbertRep_coe]
    exact (WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).continuous.continuousAt.tendsto.comp ht
  have hE := GradientCore.tendsto_energy_of_coe ha htc
  refine ⟨u, ?_, hm⟩
  refine ⟨hu.1, hu.2.1, fun n => (f n).val, hs, ?_, ?_, ?_⟩
  · exact smoothGraph_cauchy hV.isOpen ha ht.cauchySeq
  · intro K _ hKV
    exact local_l1_of_global (fun n => (f n).property.2.1) hi htu hKV
  · change Tendsto (fun n => weightedEnergy a V
      (smoothGrad (f n).val - (gradientHilbertRep ha x.snd).field)) atTop (𝓝 0)
    simpa only [smoothEnergyField_field] using hE

/-- The supported graph represents literal zero-boundary pairs. -/
theorem zeroGraph_exists_rep [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (x : zeroGraphSubmodule hV.isOpen ha) :
    ∃ u : Vec d → ℝ, MemH1a0 a V u (gradientHilbertRep ha x.val.snd).field ∧
      volumeAverage V u = x.val.fst := by
  obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp x.property
  choose f hf using hy
  have htf : Tendsto (fun n => supportedGraphMap hV.isOpen ha (f n)) atTop (𝓝 x.val) := by
    simpa only [hf] using ht
  let s : ℕ → smoothCoreSubmodule hV.isOpen ha := fun n => supportedToSmooth hV.isOpen ha (f n)
  have hts : Tendsto (fun n => smoothGraphMap hV.isOpen ha (s n)) atTop (𝓝 x.val) := htf
  exact memH1a0_of_smoothGraph_tendsto hV hne ha (f := s) (fun n => (f n).property) hts

/-- Zero-boundary approximations converge in the graph and in value L¹. -/
theorem MemH1a0.supportedGraph_tendsto [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a0 a V u G) :
    ∃ f : ℕ → supportedCoreSubmodule V,
      Tendsto (fun n => supportedGraphMap hV.isOpen ha (f n)) atTop
        (𝓝 (WithLp.toLp 2 (volumeAverage V u,
          (memH1aEnergyField hV.isOpen ha (hu.memH1a ha) : GradientHilbert ha)))) ∧
      Tendsto (fun n => eLpNorm ((f n).val - u) 1 (volume.restrict V)) atTop (𝓝 0) := by
  have hdata := hu
  obtain ⟨huM, _, φ, hφ, hc, hlocal, henergy⟩ := hdata
  have hcore (n : ℕ) := isSmoothCore_of_supported ha (hφ n).1 (hφ n).2.1
  have hL := core_tendsto_l1 hV hne ha hcore hc huM hlocal
  let f : ℕ → supportedCoreSubmodule V := fun n => ⟨φ n, hφ n⟩
  let s : ℕ → smoothCoreSubmodule hV.isOpen ha := fun n => supportedToSmooth hV.isOpen ha (f n)
  have ht : Tendsto (fun n => supportedGraphMap hV.isOpen ha (f n)) atTop
      (𝓝 (WithLp.toLp 2 (volumeAverage V u,
        (memH1aEnergyField hV.isOpen ha (hu.memH1a ha) : GradientHilbert ha)))) :=
    smoothGraph_tendsto_of_l1_energy hV.isOpen ha (f := s) hL.2 henergy
  exact ⟨f, ht, hL.2⟩

/-- Every zero-boundary pair belongs to the closed supported graph. -/
theorem MemH1a0.graph_mem [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) :
    WithLp.toLp 2 (volumeAverage V u,
      (memH1aEnergyField hV.isOpen ha (hu.memH1a ha) : GradientHilbert ha)) ∈
        zeroGraphSubmodule hV.isOpen ha := by
  obtain ⟨f, ht, _⟩ := hu.supportedGraph_tendsto hV hne ha
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
    (Eventually.of_forall fun n => subset_closure ⟨f n, rfl⟩)

/-- Gradient projection from the closed supported graph. -/
noncomputable def zeroGradientMap (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    zeroGraphSubmodule hV ha →L[ℝ] GradientHilbert ha :=
  (WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).comp (zeroGraphSubmodule hV ha).subtypeL

/-- The zero-boundary gradient map has a bounded inverse on its range. -/
theorem zeroGradientMap_antilipschitz [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) :
    ∃ K : NNReal, AntilipschitzWith K (zeroGradientMap hV.isOpen ha) := by
  obtain ⟨C, hC, hb⟩ := exists_memH1a0_coercivity hV hne
  let K : NNReal := ⟨1 + C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace),
    add_nonneg zero_le_one (mul_nonneg hC (Real.sqrt_nonneg _))⟩
  refine ⟨K, ContinuousLinearMap.antilipschitz_of_bound _ ?_⟩
  intro x
  obtain ⟨u, hu, hm⟩ := zeroGraph_exists_rep hV hne ha x
  have hmean := (hb a ha u _ hu).2.2.1
  have he : Real.sqrt (weightedEnergy a V (gradientHilbertRep ha x.val.snd).field).toReal =
      ‖x.val.snd‖ := by
    rw [← GradientCore.norm_sq ha, Real.sqrt_sq (norm_nonneg _),
      ← UniformSpace.Completion.norm_coe, gradientHilbertRep_coe]
  rw [he, hm] at hmean
  have hnorm : ‖x‖ ≤ |x.val.fst| + ‖x.val.snd‖ := by
    apply le_of_sq_le_sq _ (add_nonneg (abs_nonneg _) (norm_nonneg _))
    change ‖x.val‖ ^ 2 ≤ _
    rw [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs]
    nlinarith only [abs_nonneg x.val.fst, norm_nonneg x.val.snd]
  change ‖x‖ ≤ (1 + C * Real.sqrt (∫ x in V, ((a x)⁻¹).trace)) * ‖x.val.snd‖
  nlinarith only [hnorm, hmean]

/-- Closed zero-boundary carrier with the energy inner product inherited from gradients. -/
noncomputable abbrev zeroSubmodule (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    Submodule ℝ (GradientHilbert ha) := (zeroGradientMap hV ha).range

theorem zeroHilbert_complete [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : CompleteSpace (zeroSubmodule hV.isOpen ha) := by
  obtain ⟨K, hK⟩ := zeroGradientMap_antilipschitz hV hne ha
  exact (hK.isClosed_range (zeroGradientMap hV.isOpen ha).uniformContinuous).completeSpace_coe

/-- Every zero-boundary gradient belongs to the energy Hilbert carrier. -/
theorem MemH1a0.gradient_mem [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) :
    (memH1aEnergyField hV.isOpen ha (hu.memH1a ha) : GradientHilbert ha) ∈
      zeroSubmodule hV.isOpen ha :=
  ⟨⟨_, hu.graph_mem hV hne ha⟩, rfl⟩

/-- Every element of the energy boundary carrier has a zero-boundary pair. -/
theorem zeroHilbert_exists_rep [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (x : zeroSubmodule hV.isOpen ha) :
    ∃ u : Vec d → ℝ, MemH1a0 a V u (gradientHilbertRep ha x.val).field := by
  obtain ⟨y, hy⟩ := x.property
  obtain ⟨u, hu, _⟩ := zeroGraph_exists_rep hV hne ha y
  change y.val.snd = x.val at hy
  rw [hy] at hu
  exact ⟨u, hu⟩

end CoarseDeGiorgi.Weighted
