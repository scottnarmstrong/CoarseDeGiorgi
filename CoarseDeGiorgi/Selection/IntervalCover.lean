import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace CoarseDeGiorgi.Selection

open Set Metric MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Finite greedy interval covering with the exact dilation three.
Unlike the general countable Vitali theorem, no constant larger than three is needed. -/
theorem exists_disjoint_intervals_covering_three {ι : Type*} (s : Finset ι)
    (x r : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) :
    ∃ u : Finset ι, u ⊆ s ∧
      (u : Set ι).PairwiseDisjoint (fun i => ball (x i) (r i)) ∧
      ∀ i ∈ s, ∃ j ∈ u, ball (x i) (r i) ⊆ ball (x j) (3 * r j) := by
  classical
  induction s using Finset.strongInductionOn
  rename_i s ih
  by_cases hs : s = ∅
  · subst s
    exact ⟨∅, by simp⟩
  obtain ⟨a, ha, hmax⟩ := s.exists_max_image r (Finset.nonempty_iff_ne_empty.mpr hs)
  let t := s.filter (fun b => Disjoint (ball (x a) (r a)) (ball (x b) (r b)))
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hat : a ∉ t := by
    simp only [t, Finset.mem_filter, not_and]
    intro _
    exact fun h => Set.not_disjoint_iff.mpr ⟨x a, mem_ball_self (hr a ha), mem_ball_self (hr a ha)⟩ h
  have hproper : t ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hts, by
    intro he; exact hat (he ▸ ha)⟩
  obtain ⟨u, hut, hdis, hcover⟩ := ih t hproper (fun b hb => hr b (hts hb))
  refine ⟨insert a u, Finset.insert_subset_iff.mpr ⟨ha, hut.trans hts⟩, ?_, ?_⟩
  · simp only [Finset.coe_insert, Set.pairwiseDisjoint_insert]
    refine ⟨hdis, ?_⟩
    intro b hb _hne
    exact (Finset.mem_filter.mp (hut hb)).2
  · intro b hb
    by_cases hbt : b ∈ t
    · obtain ⟨c, hc, hbc⟩ := hcover b hbt
      exact ⟨c, Finset.mem_insert_of_mem hc, hbc⟩
    · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
      have hnot : ¬Disjoint (ball (x a) (r a)) (ball (x b) (r b)) := by
        intro hd; exact hbt (Finset.mem_filter.mpr ⟨hb, hd⟩)
      have hmeet := Set.not_disjoint_iff.mp hnot
      have hdist : dist (x b) (x a) < r a + r b := by
        rw [dist_comm]
        exact dist_lt_add_of_nonempty_ball_inter_ball ⟨hmeet.choose, hmeet.choose_spec⟩
      apply ball_subset_ball'
      have hrb := hmax b hb
      linarith

/-- Tripling an interval triples its Lebesgue measure exactly. -/
theorem volume_ball_three (x r : ℝ) :
    volume (ball x (3 * r)) = 3 * volume (ball x r) := by
  simp only [Real.ball_eq_Ioo, Real.volume_Ioo]
  have h3 : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
  rw [← h3]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring


end

end CoarseDeGiorgi.Selection
