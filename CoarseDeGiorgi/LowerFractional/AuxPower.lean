import CoarseDeGiorgi.LowerFractional.AuxTiling

/-! Exact integration of the descendant step field. -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

lemma lower_auxAverage_rpow_pointwise {d : ℕ} (m k : ℤ) (hmk : m ≤ k)
    (z : Fin d → ℤ) (G : Vec d → Vec d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    (ENNReal.ofReal (euclidNorm (auxAverage m k z G x))) ^ r =
      ∑ n ∈ auxDescendantIndices m k,
        (auxDescendantCube m k z n).indicator
          (fun _ => (ENNReal.ofReal (euclidNorm (auxDescendantAverage m k z n G))) ^ r) x := by
  classical
  by_cases hx : ∃ n ∈ auxDescendantIndices m k, x ∈ auxDescendantCube m k z n
  · obtain ⟨n, hn, hx⟩ := hx
    have hnother : ∀ v ∈ auxDescendantIndices m k, v ≠ n →
        x ∉ auxDescendantCube m k z v := by
      intro v hv hvn hxv
      exact Set.disjoint_left.mp (lower_auxDescendants_pairwiseDisjoint m k hmk z
        hn hv hvn.symm) hx hxv
    have he : auxAverage m k z G x = auxDescendantAverage m k z n G := by
      unfold auxAverage
      rw [Finset.sum_eq_single n]
      · simp only [hx, ite_true]
      · intro v hv hvn
        simp only [hnother v hv hvn, ite_false]
      · exact fun h => (h hn).elim
    rw [he, Finset.sum_eq_single n]
    · simp only [Set.indicator_of_mem hx]
    · intro v hv hvn
      exact Set.indicator_of_notMem (hnother v hv hvn) _
    · exact fun h => (h hn).elim
  · have hn : ∀ n ∈ auxDescendantIndices m k, x ∉ auxDescendantCube m k z n := by
      intro n hn hx'
      exact hx ⟨n, hn, hx'⟩
    have he : auxAverage m k z G x = 0 := by
      unfold auxAverage
      exact Finset.sum_eq_zero fun n hn' => ite_eq_right (hn n hn')
    rw [he]
    have hzero : euclidNorm (0 : Vec d) = 0 := by simp [euclidNorm, vecNormSq, vecDot]
    simp only [hzero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hr]
    exact (Finset.sum_eq_zero fun n hn' => Set.indicator_of_notMem (hn n hn') _).symm

lemma lower_auxAverage_power_integral {d : ℕ} (m k : ℤ) (hmk : m ≤ k)
    (z : Fin d → ℤ) (G : Vec d → Vec d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x in auxCube m z, (ENNReal.ofReal (euclidNorm (auxAverage m k z G x))) ^ r) =
      ENNReal.ofReal (∑ n ∈ auxDescendantIndices m k,
        (volume (auxDescendantCube m k z n)).toReal *
          euclidNorm (auxDescendantAverage m k z n G) ^ r) := by
  classical
  simp_rw [lower_auxAverage_rpow_pointwise m k hmk z G hr]
  rw [lintegral_finsetSum]
  · have hnonneg : ∀ n ∈ auxDescendantIndices m k,
        0 ≤ (volume (auxDescendantCube m k z n)).toReal *
          euclidNorm (auxDescendantAverage m k z n G) ^ r := by
      intro n hn
      exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
    apply Finset.sum_congr rfl
    intro n hn
    have hmeas : MeasurableSet (auxDescendantCube m k z n) :=
      Foundations.Reconstruction.measurableSet_auxDescendantCube m k z n
    have hvtop : volume (auxDescendantCube m k z n) ≠ ⊤ := by
      rw [← Foundations.Reconstruction.auxDescendantCube_eq_statement,
        Foundations.Reconstruction.volume_auxDescendantCube]
      exact ENNReal.ofReal_ne_top
    rw [lintegral_indicator hmeas, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Measure.restrict_apply hmeas,
      Set.inter_eq_left.mpr (lower_auxDescendant_subset m k hmk z n hn),
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hvtop, ENNReal.ofReal_rpow_of_nonneg
        (show 0 ≤ euclidNorm (auxDescendantAverage m k z n G) from Real.sqrt_nonneg _) hr.le,
      mul_comm]
  · intro n hn
    exact measurable_const.indicator
      (Foundations.Reconstruction.measurableSet_auxDescendantCube m k z n)


end CoarseDeGiorgi.LowerFractional
