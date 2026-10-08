import CoarseDeGiorgi.Weighted.TestingProducts
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped NNReal

/-- The one-sided testing step is nondecreasing. -/
theorem testing_gStep_monotone (c : ℝ) {δ : ℝ} (hδ : 0 < δ) : Monotone (gStep c δ) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact sub_le_sub_right (div_le_div_of_nonneg_right (sub_le_sub_right hxy c) hδ.le) 1

/-- The derivative of the one-sided testing step is nonnegative. -/
theorem testing_gStep_deriv_nonneg (c : ℝ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ deriv (gStep c δ) t := (testing_gStep_monotone c hδ).deriv_nonneg

/-- A fixed smooth testing step has a bounded derivative. -/
theorem testing_gStep_deriv_bounded (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : ℝ≥0, ∀ t, |deriv (gStep c δ) t| ≤ L := by
  have hd := (gStep_contDiff c δ).continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hd.norm.continuousOn
    (K := Set.Icc (c + δ) (c + 2 * δ))
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (c + δ) (c + 2 * δ)
  · exact (show ‖deriv (gStep c δ) t‖ ≤ C from hC ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · have hzero : deriv (gStep c δ) t = 0 := by
      rcases lt_or_ge t (c + δ) with hlo | hlo
      · have heq : gStep c δ =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
          filter_upwards [eventually_lt_nhds hlo] with s hs
          exact gStep_eq_zero hδ hs.le
        exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq |>.deriv
      · have hhi : c + 2 * δ < t := by
          exact lt_of_not_ge (fun h => ht ⟨hlo, h⟩)
        have heq : gStep c δ =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
          filter_upwards [eventually_gt_nhds hhi] with s hs
          exact gStep_eq_one hδ hs.le
        exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq |>.deriv
    rw [hzero, abs_zero]
    exact le_max_right _ _


end CoarseDeGiorgi.Weighted
