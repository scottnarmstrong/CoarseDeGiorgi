module

public import CoarseDeGiorgi.Whitney.SeedProjection
public import CoarseDeGiorgi.Statements.WhitneyCubesProperties

/-! # The active Whitney collar -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization Set

noncomputable section

variable {d : ℕ}

theorem seedWhitney_gap_bounds {τ : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    {D : TriadicCube d} (hD : D ∈ whitneyCubes τ) {x : Vec d}
    (hx : x ∈ closedTriadicCube D) :
    2 * cubeScaleFactor D < seedGap τ x ∧ seedGap τ x ≤ 9 * cubeScaleFactor D := by
  have hdist := (CoarseDeGiorgi.whitney_cubes hτ hτ1).2.2.2 D hD x hx
  have hpoint := hdist.1.trans_le hdist.2.1
  rw [seedPointDistance_eq (by linarith only [hτ])] at hpoint hdist
  have hpos : 0 < max 0 (seedGap τ x) :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) (Foundations.Triadic.scaleFactor_pos D)).trans hpoint
  have hgap : 0 < seedGap τ x := (lt_max_iff.mp hpos).resolve_left (lt_irrefl _)
  rw [max_eq_right hgap.le] at hpoint hdist
  exact ⟨hpoint, hdist.2.2⟩

theorem seedCellScale_parent (cell : SeedCell d) :
    cubeScaleFactor cell.cube = 3 * seedCellScale cell := by
  have hp := zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0) (cell.cube.scale - 1)
  rw [sub_add_cancel] at hp
  change (3 : ℝ) ^ cell.cube.scale = 3 * (3 : ℝ) ^ (cell.cube.scale - 1)
  exact hp.trans (mul_comm _ _)

end

end CoarseDeGiorgi.Whitney

