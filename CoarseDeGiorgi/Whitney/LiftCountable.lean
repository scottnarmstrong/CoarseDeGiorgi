module

public import CoarseDeGiorgi.Whitney.LiftSums

@[expose] public section

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators
noncomputable section
variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Finite total cell energy makes disjoint partial sums Cauchy in energy. -/
lemma lift_disjoint_energy_cauchy (ha : IsWeightedCoeffOn V a)
    (U : ℕ → Set (Vec d)) (G : ℕ → Vec d → Vec d)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hM : ∀ k, AEStronglyMeasurable (G k) (volume.restrict V))
    (hsupp : ∀ k x, x ∉ U k → G k x = 0)
    (hsum : (∑' k, weightedEnergy a V (G k)) ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      weightedEnergy a V ((∑ k ∈ Finset.range m, G k) - (∑ k ∈ Finset.range n, G k)) <
        ENNReal.ofReal ε := by
  classical
  intro ε hε
  let E (k : ℕ) := weightedEnergy a V (G k)
  have ht := ENNReal.tendsto_tsum_compl_atTop_zero hsum
  have hev := ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨S, hS⟩ := hev.exists
  obtain ⟨N, hSN⟩ := S.exists_nat_subset_range
  refine ⟨N, ?_⟩
  have hbound (m n : ℕ) (hnm : n ≤ m) (hn : N ≤ n) :
      weightedEnergy a V ((∑ k ∈ Finset.range m, G k) - (∑ k ∈ Finset.range n, G k)) < ENNReal.ofReal ε := by
    have hdiff : (∑ k ∈ Finset.range m, G k) - (∑ k ∈ Finset.range n, G k) =
        ∑ k ∈ Finset.range m \ Finset.range n, G k := by
      apply sub_eq_iff_eq_add.mpr
      exact (Finset.sum_sdiff (Finset.range_mono hnm)).symm
    rw [hdiff, lift_energy_finset_disjoint ha U G hdisj hM hsupp]
    have hout (k : ℕ) (hk : k ∈ Finset.range m \ Finset.range n) : k ∉ S := by
      intro hkS
      exact (Finset.mem_sdiff.mp hk).2 ((Finset.range_mono hn) (hSN hkS))
    calc
      _ = ∑ k ∈ Finset.range m \ Finset.range n, {k : ℕ | k ∉ S}.indicator E k := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (indicator_of_mem (hout k hk) E).symm
      _ ≤ ∑' k, {k : ℕ | k ∉ S}.indicator E k := ENNReal.sum_le_tsum _
      _ = ∑' k : {k : ℕ // k ∉ S}, E k := (tsum_subtype _ E).symm
      _ < _ := hS
  intro m n hm hn
  rcases le_total n m with hnm | hmn
  · exact hbound m n hnm hn
  · have hneg : weightedEnergy a V ((∑ k ∈ Finset.range m, G k) - (∑ k ∈ Finset.range n, G k)) =
        weightedEnergy a V ((∑ k ∈ Finset.range n, G k) - (∑ k ∈ Finset.range m, G k)) := by
      rw [show (∑ k ∈ Finset.range m, G k) - (∑ k ∈ Finset.range n, G k) =
          -((∑ k ∈ Finset.range n, G k) - (∑ k ∈ Finset.range m, G k)) by abel]
      exact Weighted.energy_neg _
    rw [hneg]
    exact hbound n m hmn hm

/-- Countably many disjoint cell corrections have an ambient boundary limit.
Summability here is of the actual correction energies, not the layer estimate. -/
theorem lift_countable_boundary_limit [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a)
    (U : ℕ → Set (Vec d)) (u : ℕ → Vec d → ℝ) (G : ℕ → Vec d → Vec d)
    (hu : ∀ k, MemH1a0 a V (u k) (G k))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hsupp : ∀ k x, x ∉ U k → G k x = 0)
    (hsum : (∑' k, weightedEnergy a V (G k)) ≠ ⊤) :
    ∃ w H, MemH1a0 a V w H ∧
      Tendsto (fun n => weightedEnergy a V ((∑ k ∈ Finset.range n, G k) - H)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm ((∑ k ∈ Finset.range n, u k) - w) 1 (volume.restrict V)) atTop (𝓝 0) := by
  apply lift_boundary_limit hV hne ha
    (fun n => lift_boundary_finset_sum hV hne ha u G hu (Finset.range n))
  exact lift_disjoint_energy_cauchy ha U G hdisj (fun k => (hu k).2.1) hsupp hsum

end
end CoarseDeGiorgi.Whitney
