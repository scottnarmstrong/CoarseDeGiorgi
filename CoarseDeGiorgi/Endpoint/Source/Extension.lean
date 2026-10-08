import CoarseDeGiorgi.Endpoint.Source.Continuity
import CoarseDeGiorgi.Endpoint.Source.Potential
import CoarseDeGiorgi.Weighted.TestingNonnegative

/-! Extension of the source and potential equations to nonnegative zero-boundary tests. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology
open CoarseDeGiorgi.Weighted

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The flux pairing of supported smooth approximants converges to the pairing of the limit. -/
theorem pairing_tendsto [NeZero d] (hV : IsOpenBoundedConvexDomain V) (ha : IsWeightedCoeffOn V a)
    {g : Vec d → ℝ} {H : Vec d → Vec d} (hg : MemH1a0 a V g H)
    {f : ℕ → Vec d → ℝ}
    (hf : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ V)
    (hE : Tendsto (fun n => Weighted.weightedEnergy a V (Weighted.smoothGrad (f n) - H)) atTop (𝓝 0))
    {X : Vec d → Vec d} (hX : AEStronglyMeasurable X (volume.restrict V))
    (hEX : Weighted.weightedEnergy a V X < ⊤) :
    Tendsto (fun n => fluxPairing a V X (f n)) atTop
      (𝓝 (∫ x in V, vecDot (H x) (matVecMul (a x) (X x)))) := by
  have hcore := fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
  let K := memH1aEnergyField hV.isOpen ha (Weighted.MemH1a0.memH1a ha hg)
  have htG : Tendsto (fun n => (smoothEnergyField hV.isOpen ha (hcore n) : GradientHilbert ha))
      atTop (𝓝 (K : GradientHilbert ha)) := GradientCore.tendsto_coe_of_energy ha
        (F := fun n => smoothEnergyField hV.isOpen ha (hcore n)) (G := K) hE
  have htI := htG.inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := ((energyField ha hX hEX : GradientCore ha) : GradientHilbert ha)))
  simp only [gradientHilbert_inner_coe] at htI
  exact htI

/-- A nonnegative zero-boundary test pairs nonnegatively with the potential, and the source
dominates the restriction. -/
theorem nonneg_pairing [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {μ ν : Measure (Vec d)} [IsFiniteMeasure ν]
    (hμν : ν ≤ μ)
    (hμ : ∀ K : Set (Vec d), IsCompact K → K ⊆ V → μ K < ⊤)
    {G Gv : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : Weighted.weightedEnergy a V G < ⊤)
    (hGv : AEStronglyMeasurable Gv (volume.restrict V))
    (hEGv : Weighted.weightedEnergy a V Gv < ⊤)
    (hrep : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x, φ x ∂μ = fluxPairing a V G φ)
    (heq : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → fluxPairing a V Gv φ = ∫ x, φ x ∂ν)
    {g : Vec d → ℝ} {H : Vec d → Vec d} (hg : MemH1a0 a V g H)
    (hnn : ∀ᵐ x ∂volume.restrict V, 0 ≤ g x) :
    0 ≤ ∫ x in V, vecDot (H x) (matVecMul (a x) (Gv x)) ∧
      (∫ x in V, vecDot (H x) (matVecMul (a x) (Gv x))) ≤
        ∫ x in V, vecDot (H x) (matVecMul (a x) (G x)) := by
  obtain ⟨f, hf, -, hE⟩ := MemH1a0.nonnegative_approximation hV hne ha hg hnn
  have hf' : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ V :=
    fun n => ⟨(hf n).1, (hf n).2.1, (hf n).2.2.1⟩
  have t1 := pairing_tendsto hV ha hg hf' hE hGv hEGv
  have t2 := pairing_tendsto hV ha hg hf' hE hG hEG
  have hint : ∀ n, Integrable (f n) μ := fun n =>
    integrable_of_supported hμ (hf' n).2.1 (hf' n).2.2 (hf' n).1.continuous
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  refine ⟨ge_of_tendsto' t1 fun n => ?_, le_of_tendsto_of_tendsto' t1 t2 fun n => ?_⟩
  · rw [heq _ (hf' n).1 (hf' n).2.1 (hf' n).2.2]
    exact integral_nonneg (hf n).2.2.2
  · rw [heq _ (hf' n).1 (hf' n).2.1 (hf' n).2.2, ← hrep _ (hf' n).1 (hf' n).2.1 (hf' n).2.2]
    exact integral_mono_measure hμν (ae_of_all _ (hf n).2.2.2) (hint n)

end CoarseDeGiorgi.Endpoint
