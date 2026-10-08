module

public import CoarseDeGiorgi.Whitney.SeedData
public import CoarseDeGiorgi.Foundations.Euclid.Basic

/-! # Geometry and measurability of the nodal surface patches -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory Set

noncomputable section

variable {d : ℕ}

theorem norm_sub_seedProjection_le {τ : ℝ} (hτ : 0 ≤ τ) (x : Vec d) :
    ‖x - seedProjection τ x‖ ≤ max 0 (seedGap τ x) := by
  apply (pi_norm_le_iff_of_nonneg (le_max_left _ _)).mpr
  intro i
  have hi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  change |x i - max (-τ / 2) (min (x i) (τ / 2))| ≤ max 0 (‖x‖ - τ / 2)
  by_cases hl : x i ≤ -τ / 2
  · have hu : x i ≤ τ / 2 := by linarith only [hl, hτ]
    rw [min_eq_left hu, max_eq_left hl, abs_of_nonpos (by linarith only [hl])]
    have hn := (abs_le.mp hi).1
    have hm : ‖x‖ - τ / 2 ≤ max 0 (‖x‖ - τ / 2) := le_max_right _ _
    linarith only [hn, hm]
  · by_cases hu : τ / 2 ≤ x i
    · rw [min_eq_right hu, max_eq_right (by linarith only [hτ]),
        abs_of_nonneg (by linarith only [hu])]
      have hn := (abs_le.mp hi).2
      exact (sub_le_sub_right hn _).trans (le_max_right _ _)
    · rw [min_eq_left (le_of_not_ge hu), max_eq_right (le_of_not_ge hl), sub_self, abs_zero]
      exact le_max_left _ _

theorem seedPointDistance_eq {τ : ℝ} (hτ : 0 ≤ τ) (x : Vec d) :
    pointSupDist x (closedReferenceCube τ) = max 0 (seedGap τ x) := by
  rw [Foundations.Triadic.pointSupDist_eq_infDist]
  have hproj : seedProjection τ x ∈ closedReferenceCube τ :=
    seedProjection_coordinate_bound hτ x
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem hproj).trans
      (by simpa only [dist_eq_norm] using norm_sub_seedProjection_le hτ x)
  · apply max_le Metric.infDist_nonneg
    apply (Metric.le_infDist ⟨seedProjection τ x, hproj⟩).mpr
    intro y hy
    have hny : ‖y‖ ≤ τ / 2 := (pi_norm_le_iff_of_nonneg
      (div_nonneg hτ (by norm_num))).mpr (fun i => by
        simpa only [Real.norm_eq_abs] using hy i)
    have hn := norm_add_le (x - y) y
    rw [sub_add_cancel] at hn
    rw [dist_eq_norm]
    unfold seedGap
    linarith only [hn, hny]

end

end CoarseDeGiorgi.Whitney

