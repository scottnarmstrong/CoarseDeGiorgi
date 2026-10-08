module

public import CoarseDeGiorgi.LowerFractional.TilingBridge
public import CoarseDeGiorgi.LowerFractional.AverageContraction

/-! Actual descendant averages, obtained from the proved global incidence
bridge and the simplex response weights (`l.lower.averages`). -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set Aliases
open scoped BigOperators ENNReal

noncomputable section

lemma lower_paramR_gt_one {q : ℝ} (hq : 1 < q) : 1 < paramR q := by
  unfold paramR
  rw [lt_div_iff₀ (by linarith : 0 < q + 1)]
  linarith

lemma lower_descendant_average_eq {d : ℕ} (m k : ℤ) (z n : Fin d → ℤ)
    (G : Vec d → Vec d) :
    auxDescendantAverage m k z n G = volumeAverageVec (auxDescendantCube m k z n) G := by
  funext i
  unfold volumeAverageVec volumeAverage auxDescendantAverage
  have hv : volume (auxDescendantCube m k z n) =
      ENNReal.ofReal (((3 : ℝ) ^ (1 - k)) ^ d) :=
    Foundations.Reconstruction.volume_auxDescendantCube m k z n
  rw [hv, ENNReal.toReal_ofReal (by positivity)]

/-- The spatial sum over all actual descendants is controlled by the actual
lowerCellAverage. There are no assumed tilings or assumed analytic estimates. -/
theorem lower_descendant_spatial_holder {d : ℕ} [NeZero d] (m : ℤ) (k : ℕ)
    (hmk : m ≤ (k : ℤ)) (z : Fin d → ℤ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a)
    (hQ : auxCube m z ⊆ Aliases.originCube 1)
    (haQ : IsWeightedCoeffOn (auxCube m z) a)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : MemH1a a (auxCube m z) w G)
    {q : ℝ} (hq : 1 < q) :
    (∑ n ∈ auxDescendantIndices m (k : ℤ),
      (volume (auxDescendantCube m (k : ℤ) z n)).toReal *
        euclidNorm (auxDescendantAverage m (k : ℤ) z n G) ^ paramR q) ≤
      lowerCellAverage a ha k q ^ (paramR q / (2 * q)) *
        (weightedEnergy a (auxCube m z) G).toReal ^ (paramR q / 2) := by
  classical
  let I := auxDescendantIndices (d := d) m (k : ℤ)
  have ht : ∀ n ∈ I, ∃ s : Finset (SimplexIndex d k),
      (∀ η ∈ s, simplexCell k η ⊆ auxDescendantCube m (k : ℤ) z n) ∧
      (s : Set (SimplexIndex d k)).PairwiseDisjoint (simplexCell k) ∧
      (⋃ η ∈ s, simplexCell k η) =ᵐ[volume] auxDescendantCube m (k : ℤ) z n := by
    intro n hn
    obtain ⟨s, _, hs⟩ := lower_descendant_simplex_tiling m k hmk z n hn hQ
    exact ⟨s, hs⟩
  choose s hsub hdisj hcover using ht
  let cells : (Fin d → ℤ) → Finset (SimplexIndex d k) := fun n =>
    if hn : n ∈ I then s n hn else ∅
  have hcsub : ∀ n ∈ I, ∀ η ∈ cells n,
      simplexCell k η ⊆ auxDescendantCube m (k : ℤ) z n := by
    intro n hn
    simpa only [cells, dite_eq_left hn] using hsub n hn
  have hcdisj : ∀ n ∈ I,
      (cells n : Set (SimplexIndex d k)).PairwiseDisjoint (simplexCell k) := by
    intro n hn
    simpa only [cells, dite_eq_left hn] using hdisj n hn
  have hccover : ∀ n ∈ I, (⋃ η ∈ cells n, simplexCell k η) =ᵐ[volume]
      auxDescendantCube m (k : ℤ) z n := by
    intro n hn
    simpa only [cells, dite_eq_left hn] using hcover n hn
  let S := I.biUnion cells
  have hSsub : ∀ η ∈ S, simplexCell k η ⊆ auxCube m z := by
    intro η hη
    obtain ⟨n, hn, hη⟩ := Finset.mem_biUnion.mp hη
    exact (hcsub n hn η hη).trans (lower_auxDescendant_subset m (k : ℤ) hmk z n hn)
  have hSdisj : (S : Set (SimplexIndex d k)).PairwiseDisjoint (simplexCell k) := by
    intro η hη ξ hξ hne
    obtain ⟨n, hn, hη⟩ := Finset.mem_biUnion.mp hη
    obtain ⟨v, hv, hξ⟩ := Finset.mem_biUnion.mp hξ
    by_cases hnv : n = v
    · subst v
      exact hcdisj n hn hη hξ hne
    · exact (lower_auxDescendants_pairwiseDisjoint m (k : ℤ) hmk z hn hv hnv).mono
        (hcsub n hn η hη) (hcsub v hv ξ hξ)
  have hsum := lower_simplex_spatial_holder k a ha
    (auxCube_isOpenBoundedConvexDomain m z) (auxCube_nonempty m z) haQ hw S hSsub hSdisj hq
  have hW := Weighted.memH1a_memW11 (auxCube_isOpenBoundedConvexDomain m z)
    (auxCube_nonempty m z) haQ hw
  have hG : IntegrableOn G (auxCube m z) := Integrable.of_eval hW.2.1
  have hstep : ∀ n ∈ I,
      (volume (auxDescendantCube m (k : ℤ) z n)).toReal *
          euclidNorm (auxDescendantAverage m (k : ℤ) z n G) ^ paramR q ≤
        ∑ η ∈ cells n, (volume (simplexCell k η)).toReal *
          euclidNorm (volumeAverageVec (simplexCell k η) G) ^ paramR q := by
    intro n hn
    rw [lower_descendant_average_eq]
    apply lower_simplex_tiling_mean_rpow k (cells n)
      (hG.mono_set (lower_auxDescendant_subset m (k : ℤ) hmk z n hn))
    · rw [← Foundations.Reconstruction.auxDescendantCube_eq_statement,
        Foundations.Reconstruction.volume_auxDescendantCube]
      exact (ENNReal.ofReal_pos.mpr
        (pow_pos (Foundations.Reconstruction.auxSide_pos _) d)).ne'
    · rw [← Foundations.Reconstruction.auxDescendantCube_eq_statement,
        Foundations.Reconstruction.volume_auxDescendantCube]
      exact ENNReal.ofReal_ne_top
    · exact hcsub n hn
    · exact hcdisj n hn
    · exact hccover n hn
    · exact (lower_paramR_gt_one hq).le
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.sum_biUnion (lower_descendant_cell_incidence_disjoint m k hmk z cells hcsub)]
  exact hsum


end

end CoarseDeGiorgi.LowerFractional
