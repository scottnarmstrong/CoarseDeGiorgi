import CoarseDeGiorgi.Whitney.Harmonic.Geometry
import CoarseDeGiorgi.Whitney.SourceWitnessResponse
import CoarseDeGiorgi.Statements.SimplexIndex
import CoarseDeGiorgi.Statements.SimplexCell
import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize
import CoarseDeGiorgi.Statements.EuclideanSetDistance
import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Statements.SampledUpperResponse

/-! Near cells are sampled by the response maximum. -/

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

/-- A point outside the cube at sup-distance `r` from it is at sup-distance `≤ r` of the surface. -/
theorem exists_surface_point_close {τ : ℝ} (hτ : 0 < τ) {x : Vec d}
    (hx : x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) τ) :
    ∃ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ,
      dist x y ≤ CoarseDeGiorgi.pointSupDist x (CoarseDeGiorgi.closedReferenceCube (d := d) τ) := by
  have hxn : τ / 2 < ‖x‖ := by
    rw [closedRef_eq_closedBall hτ.le, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hx
  have hxpos : 0 < ‖x‖ := by linarith
  refine ⟨((τ / 2) / ‖x‖) • x, ?_, ?_⟩
  · change ‖((τ / 2) / ‖x‖) • x‖ = τ / 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  · have hdist : dist x (((τ / 2) / ‖x‖) • x) = ‖x‖ - τ / 2 := by
      rw [dist_eq_norm]
      have : x - ((τ / 2) / ‖x‖) • x = (1 - (τ / 2) / ‖x‖) • x := by
        rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      · field_simp
      · rw [sub_nonneg, div_le_one hxpos]; linarith
    rw [hdist]
    have hne : (CoarseDeGiorgi.closedReferenceCube (d := d) τ).Nonempty :=
      ⟨0, by rw [closedRef_eq_closedBall hτ.le]; simp; linarith⟩
    apply le_csInf (hne.image _)
    rintro _ ⟨z, hz, rfl⟩
    rw [closedRef_eq_closedBall hτ.le, Metric.mem_closedBall, dist_zero_right] at hz
    have := norm_sub_norm_le x z
    rw [← dist_eq_norm] at this
    linarith

/-- The cell closure is within `100 d 3^{-j}` of the surface. -/
theorem euclideanSetDistance_cell_le {τ : ℝ} (hτ0 : 1 / 2 ≤ τ) (hτ1 : τ < 1) (hd : 1 ≤ d)
    (j : ℕ) (cell : CoarseDeGiorgi.ExteriorCell d τ) (hs : cell.1.val.scale = 1 - (j : ℤ)) :
    CoarseDeGiorgi.euclideanSetDistance (closure (CoarseDeGiorgi.exteriorCellSet cell))
      (CoarseDeGiorgi.cubeSurface (d := d) τ) ≤
      ENNReal.ofReal (100 * (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ))) := by
  have hτpos : 0 < τ := by linarith
  have hne : (CoarseDeGiorgi.exteriorCellSet cell).Nonempty := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_nonempty (whitneyCell cell)
  obtain ⟨x, hx⟩ := hne
  have hxc := cell_subset_closedCube cell hx
  obtain ⟨_, _, hC⟩ := (CoarseDeGiorgi.whitney_cubes hτ0 hτ1).2.2.2 cell.1.1 cell.1.2 x hxc
  have hxB : x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) τ :=
    fun hb => (Set.disjoint_left.mp (cell_disjoint_closedRef hτ0 hτ1 cell)) hx hb
  obtain ⟨y, hy, hxy⟩ := exists_surface_point_close hτpos hxB
  have hu : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℤ)) := zpow_pos (by norm_num) _
  have hℓ : cubeScaleFactor cell.1.1 = 3 * (3 : ℝ) ^ (-(j : ℤ)) := by
    unfold cubeScaleFactor
    rw [hs, show (1 - (j : ℤ)) = 1 + (-(j : ℤ)) by ring, zpow_add₀ (by norm_num)]
    simp
  have hdd : (d : ℝ) ≥ 1 := by exact_mod_cast hd
  have hsq : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have heu : CoarseDeGiorgi.euclidDist x y ≤ 100 * (d : ℝ) * (3 : ℝ) ^ (-(j : ℤ)) := by
    have h1 : CoarseDeGiorgi.euclidDist x y ≤ Real.sqrt d * dist x y :=
      Foundations.Euclid.eDist2_le_sqrt_mul_dist x y
    have h2 : dist x y ≤ 9 * (3 * (3 : ℝ) ^ (-(j : ℤ))) := by
      rw [← hℓ]; linarith
    calc CoarseDeGiorgi.euclidDist x y ≤ Real.sqrt d * dist x y := h1
      _ ≤ Real.sqrt d * (9 * (3 * (3 : ℝ) ^ (-(j : ℤ)))) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ ≤ d * (9 * (3 * (3 : ℝ) ^ (-(j : ℤ)))) := by gcongr
      _ ≤ _ := by nlinarith
  unfold CoarseDeGiorgi.euclideanSetDistance
  refine (iInf₂_le x (subset_closure hx)).trans ?_
  refine (iInf₂_le y hy).trans ?_
  exact ENNReal.ofReal_le_ofReal heu

end CoarseDeGiorgi.Whitney.Harmonic
