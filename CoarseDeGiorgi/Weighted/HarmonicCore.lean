module

public import CoarseDeGiorgi.Weighted.PairOperations
public import CoarseDeGiorgi.Statements.IsWeightedSolution

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A supported smooth test is a literal zero-boundary pair. -/
theorem memH1a0_of_supported (hV : IsOpen V) (_ha : IsWeightedCoeffOn V a)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ V) :
    MemH1a0 a V φ (smoothGrad φ) := by
  refine ⟨hφ.continuous.aestronglyMeasurable,
    smoothGrad_aestronglyMeasurable hV hφ.contDiffOn,
    fun _ => φ, fun _ => ⟨hφ, hc, hs⟩, ?_, ?_, ?_⟩
  · intro ε hε
    refine ⟨0, fun _ _ _ _ => ?_⟩
    simpa [volumeAverage, CoarseDeGiorgi.weightedEnergy, vecDot, matVecMul] using
      (ENNReal.ofReal_pos.mpr hε)
  · intro K _ _
    simpa only [sub_self, enorm_zero, lintegral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  · simp [CoarseDeGiorgi.weightedEnergy, vecDot, matVecMul]

/-- Smooth-test harmonicity extends to every zero-boundary pair. -/
theorem IsWeightedSolution.orthogonality [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    {u w : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : CoarseDeGiorgi.IsWeightedSolution a V u G) (hw : MemH1a0 a V w H) :
    IntegrableOn (fun x => vecDot (H x) (matVecMul (a x) (G x))) V ∧
      (∫ x in V, vecDot (H x) (matVecMul (a x) (G x))) = 0 := by
  let F := memH1aEnergyField hV.isOpen ha hu.1
  let K := memH1aEnergyField hV.isOpen ha (hw.memH1a ha)
  obtain ⟨f, htf, _⟩ := hw.supportedGraph_tendsto hV hne ha
  let s : ℕ → smoothCoreSubmodule hV.isOpen ha := fun n => supportedToSmooth hV.isOpen ha (f n)
  have htG : Tendsto (fun n => (smoothEnergyField hV.isOpen ha (s n).property : GradientHilbert ha))
      atTop (𝓝 (K : GradientHilbert ha)) :=
    (WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).continuous.continuousAt.tendsto.comp htf
  have htI := htG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := (F : GradientHilbert ha)))
  have he (n : ℕ) : inner ℝ (smoothEnergyField hV.isOpen ha (s n).property : GradientHilbert ha)
      (F : GradientHilbert ha) = 0 := by
    rw [gradientHilbert_inner_coe]
    exact (hu.2 (f n).val (f n).property.1 (f n).property.2.1 (f n).property.2.2).2
  have hzero : inner ℝ (K : GradientHilbert ha) (F : GradientHilbert ha) = 0 := by
    exact tendsto_nhds_unique htI (by simpa only [he] using tendsto_const_nhds)
  refine ⟨(pairing_integrable_and_bound ha hw.2.1 hu.1.2.1
    ((hw.memH1a ha).energy_lt_top hV.isOpen ha) (MemH1a.energy_lt_top hV.isOpen ha hu.1)).1, ?_⟩
  rw [gradientHilbert_inner_coe] at hzero
  exact hzero

/-- Orthogonality to all zero-boundary pairs gives the weighted solution predicate. -/
theorem isWeightedSolution_of_orthogonality (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G)
    (hortho : ∀ w H, MemH1a0 a V w H →
      (∫ x in V, vecDot (H x) (matVecMul (a x) (G x))) = 0) :
    CoarseDeGiorgi.IsWeightedSolution a V u G := by
  refine ⟨hu, fun φ hφ hc hs => ?_⟩
  have hcore := isSmoothCore_of_supported ha hφ hc
  exact ⟨(pairing_integrable_and_bound ha
    (smoothGrad_aestronglyMeasurable hV hφ.contDiffOn) hu.2.1
    hcore.2.2 (hu.energy_lt_top hV ha)).1,
    hortho φ (smoothGrad φ) (memH1a0_of_supported hV ha hφ hc hs)⟩

end CoarseDeGiorgi.Weighted
