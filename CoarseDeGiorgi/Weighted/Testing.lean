import CoarseDeGiorgi.Weighted.TestingNonnegative
import CoarseDeGiorgi.Weighted.HarmonicCore
import CoarseDeGiorgi.Statements.Csub
import CoarseDeGiorgi.Statements.Csol

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The subsolution inequality extends to every nonnegative zero-boundary test,
without requiring the test to be bounded. -/
theorem IsWeightedSubsolution.testing (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u g : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : CoarseDeGiorgi.IsWeightedSubsolution a V u G) (hg : MemH1a0 a V g H)
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ g x) :
    IntegrableOn (fun x => vecDot (H x) (matVecMul (a x) (G x))) V ∧
      (∫ x in V, vecDot (H x) (matVecMul (a x) (G x))) ≤ 0 := by
  let F := memH1aEnergyField hV.isOpen ha hu.1
  let K := memH1aEnergyField hV.isOpen ha (hg.memH1a ha)
  obtain ⟨f, hf, _, hE⟩ := MemH1a0.nonnegative_approximation hV hne ha hg hnonneg
  have hcore := fun n => isSmoothCore_of_supported ha (hf n).1 (hf n).2.1
  have htG : Tendsto (fun n => (smoothEnergyField hV.isOpen ha (hcore n) : GradientHilbert ha))
      atTop (𝓝 (K : GradientHilbert ha)) := GradientCore.tendsto_coe_of_energy ha
        (F := fun n => smoothEnergyField hV.isOpen ha (hcore n)) (G := K) hE
  have htI := htG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := (F : GradientHilbert ha)))
  have hle (n : ℕ) : inner ℝ (smoothEnergyField hV.isOpen ha (hcore n) : GradientHilbert ha)
      (F : GradientHilbert ha) ≤ 0 := by
    rw [gradientHilbert_inner_coe]
    exact (hu.2 (f n) (hf n).1 (hf n).2.1 (hf n).2.2.1 (hf n).2.2.2).2
  have hlim : inner ℝ (K : GradientHilbert ha) (F : GradientHilbert ha) ≤ 0 :=
    le_of_tendsto htI (Eventually.of_forall hle)
  refine ⟨(pairing_integrable_and_bound ha hg.2.1 hu.1.2.1
    ((hg.memH1a ha).energy_lt_top hV.isOpen ha) (MemH1a.energy_lt_top hV.isOpen ha hu.1)).1, ?_⟩
  rw [gradientHilbert_inner_coe] at hlim
  exact hlim



end CoarseDeGiorgi.Weighted
