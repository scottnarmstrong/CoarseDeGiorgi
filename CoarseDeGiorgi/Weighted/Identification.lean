module

public import CoarseDeGiorgi.Weighted.Completion

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A represented weighted Sobolev pair has finite energy. -/
theorem MemH1a.energy_lt_top (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a a V u G) :
    weightedEnergy a V G < ⊤ := by
  obtain ⟨_, hG, f, hf, _, _, ht⟩ := hu
  exact energy_lt_top_of_tendsto ha (fun n => smoothGrad_aestronglyMeasurable hV (hf n).1)
    hG (fun n => (hf n).2.2) ht

/-- Identification with W¹,¹, with the authorized positive-dimension implementation hypothesis. -/
theorem memH1a_memW11 [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a a V u G) :
    IntegrableOn u V ∧
      (∀ i : Fin d, IntegrableOn (fun x => G x i) V) ∧
      HasWeakGradientOn V u G ∧
      (∀ i : Fin d, IntegrableOn (fun x => matVecMul (a x) (G x) i) V) ∧
      weightedEnergy a V G < ⊤ := by
  have hE := hu.energy_lt_top hV.isOpen ha
  obtain ⟨huM, hGM, f, hf, hc, hloc, ht⟩ := hu
  have hFM := fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hf n).1
  have hFE := fun n => (hf n).2.2
  have hGi := coord_integrable_of_length hGM (gradient_length_integrable_and_bound ha hGM hE).1
  have hflux := coord_integrable_of_length (flux_aestronglyMeasurable ha hGM)
    (flux_length_integrable_and_bound ha hGM hE).1
  have hv := core_tendsto_l1 hV hV₀ ha hf hc huM hloc
  have hgrad := fun i => tendsto_coord_l1_of_energy ha hFM hGM hFE ht i
  have hw := hasWeakGradientOn_of_l1_limit (fun n => (hf n).2.1)
    (fun n => coord_integrable_of_length (hFM n) (gradient_length_integrable_and_bound ha (hFM n) (hFE n)).1)
    (fun n => hasWeakGradientOn_of_contDiffOn hV.isOpen (hf n).1) hv.2 hgrad
  exact ⟨hv.1, hGi, hw, hflux, hE⟩



end CoarseDeGiorgi.Weighted
