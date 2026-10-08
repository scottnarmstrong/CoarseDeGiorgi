module

public import CoarseDeGiorgi.Whitney.ExteriorCells
public import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.WhitneyCubesProperties
public import CoarseDeGiorgi.Statements.PointSupDist
public import CoarseDeGiorgi.Whitney.SourceWitnessExterior
public import CoarseDeGiorgi.Whitney.SeedClosedCover

@[expose] public section

open Homogenization MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace CoarseDeGiorgi.Whitney.Harmonic

noncomputable section

variable {d : ℕ}

open CoarseDeGiorgi.Harnack.Replacement

/-- A width `h` triadic is positive. -/
theorem triadicWidth_pos {h : ℝ} (hh : CoarseDeGiorgi.IsTriadicWidth h) : 0 < h := by
  obtain ⟨n, rfl⟩ := hh
  exact zpow_pos (by norm_num) _

/-- Any two distinct exterior cells have disjoint sets. -/
theorem exteriorCells_disjoint {τ : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (A B : CoarseDeGiorgi.ExteriorCell d τ) (hne : A ≠ B) :
    Disjoint (CoarseDeGiorgi.exteriorCellSet A) (CoarseDeGiorgi.exteriorCellSet B) := by
  rw [cellSet_eq_whitney, cellSet_eq_whitney]
  by_cases hp : (whitneyCell A).cube = (whitneyCell B).cube
  · exact Whitney.source_seedCells_same_parent_disjoint hp
      (fun he => hne (whitneyCell_injective he))
  · exact Disjoint.mono (Whitney.source_seedCell_subset_open_parent (whitneyCell A))
      (Whitney.source_seedCell_subset_open_parent (whitneyCell B))
      ((CoarseDeGiorgi.whitney_cubes hτ hτ1).1 _ A.1.2 _ B.1.2 hp)

/-- A cell lies in the closed parent cube. -/
theorem cell_subset_closedCube {τ : ℝ} (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    CoarseDeGiorgi.exteriorCellSet cell ⊆ CoarseDeGiorgi.closedTriadicCube cell.1.1 := by
  intro x hx
  rw [cellSet_eq_whitney] at hx
  have hxD := Whitney.source_seedCell_subset_open_parent (whitneyCell cell) hx
  intro i
  have := hxD i
  change (((whitneyCell cell).cube.index i : ℝ) - 1 / 2) * cubeScaleFactor (whitneyCell cell).cube < x i ∧
    x i < (((whitneyCell cell).cube.index i : ℝ) + 1 / 2) * cubeScaleFactor (whitneyCell cell).cube at this
  change |x i - ((cell.1.1.index i : ℝ) * cubeScaleFactor cell.1.1)| ≤ cubeScaleFactor cell.1.1 / 2
  have e : (whitneyCell cell).cube = cell.1.1 := rfl
  rw [e] at this
  exact abs_le.2 ⟨by nlinarith [this.1], by nlinarith [this.2]⟩

/-- Cells are disjoint from the closed reference cube. -/
theorem cell_disjoint_closedRef {τ : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    Disjoint (CoarseDeGiorgi.exteriorCellSet cell)
      (CoarseDeGiorgi.closedReferenceCube (d := d) τ) := by
  rw [Set.disjoint_left]
  intro x hx hxB
  have hxc := cell_subset_closedCube cell hx
  obtain ⟨hA, hB, _⟩ := (CoarseDeGiorgi.whitney_cubes hτ hτ1).2.2.2 cell.1.1 cell.1.2 x hxc
  have hs : 0 < cubeScaleFactor cell.1.1 := Foundations.Triadic.scaleFactor_pos _
  have : CoarseDeGiorgi.pointSupDist x (CoarseDeGiorgi.closedReferenceCube (d := d) τ) ≤ 0 := by
    apply csInf_le (⟨0, by rintro _ ⟨y, _, rfl⟩; exact dist_nonneg⟩)
    exact ⟨x, hxB, dist_self x⟩
  linarith

/-- Almost every point of the exterior of the reference cube lies in an exterior cell. -/
theorem ae_exists_cell {τ : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1) :
    ∀ᵐ x : Vec d ∂volume, x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) τ →
      ∃ cell : CoarseDeGiorgi.ExteriorCell d τ, x ∈ CoarseDeGiorgi.exteriorCellSet cell := by
  filter_upwards [Whitney.source_seed_cells_ae_interior (d := d)] with x hx hxB
  obtain ⟨D, hD, hxD⟩ := (CoarseDeGiorgi.whitney_cubes hτ hτ1).2.1 x hxB
  obtain ⟨c, hcD, hcl⟩ := Whitney.seedParent_closedCell_cover D hxD
  have hxc := hx c hcl
  have hdc : c.cube ∈ whitneyCubes τ := hcD.symm ▸ hD
  let cell : CoarseDeGiorgi.ExteriorCell d τ := ⟨⟨c.cube, hdc⟩, c.bins, c.order⟩
  refine ⟨cell, ?_⟩
  rw [cellSet_eq_whitney cell]
  exact hxc

/-- The closed reference cube is the closed sup-norm ball. -/
theorem closedRef_eq_closedBall {τ : ℝ} (hτ : 0 ≤ τ) :
    CoarseDeGiorgi.closedReferenceCube (d := d) τ = Metric.closedBall (0 : Vec d) (τ / 2) := by
  ext x
  simp only [CoarseDeGiorgi.closedReferenceCube, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ τ / 2), Real.norm_eq_abs]

theorem isClosed_closedRef {τ : ℝ} (hτ : 0 ≤ τ) :
    IsClosed (CoarseDeGiorgi.closedReferenceCube (d := d) τ) := by
  rw [closedRef_eq_closedBall hτ]; exact Metric.isClosed_closedBall

theorem isCompact_closedRef {τ : ℝ} (hτ : 0 ≤ τ) :
    IsCompact (CoarseDeGiorgi.closedReferenceCube (d := d) τ) := by
  rw [closedRef_eq_closedBall hτ]; exact isCompact_closedBall _ _

/-- The closed reference cube lies in the unit cube. -/
theorem closedRef_subset_unit {τ : ℝ} (hτ1 : τ < 1) :
    CoarseDeGiorgi.closedReferenceCube (d := d) τ ⊆ CoarseDeGiorgi.originCube 1 := by
  intro x hx i
  have := hx i
  rw [abs_le] at this
  constructor <;> linarith [this.1, this.2]

end
end CoarseDeGiorgi.Whitney.Harmonic
