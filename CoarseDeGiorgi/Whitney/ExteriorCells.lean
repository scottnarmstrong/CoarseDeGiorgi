import CoarseDeGiorgi.Whitney.SeedData
import CoarseDeGiorgi.Whitney.SourceWitnessExterior
import CoarseDeGiorgi.Moments.Cells
import CoarseDeGiorgi.Statements.ExteriorCell
import CoarseDeGiorgi.Statements.ExteriorCellCenter
import CoarseDeGiorgi.Statements.ExteriorCellSet

/-! # Exterior cells and their Whitney seed cells -/

open Homogenization MeasureTheory Set Metric

noncomputable section

namespace CoarseDeGiorgi.Whitney
variable {d : ℕ}

/-- Domain geometry of the reference cubes `originCube r`. -/
theorem source_cube_domain {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (originCube (d := d) r) := by
  rw [source_originCube_eq_ball hr]
  exact isOpenBoundedConvexDomain_ball 0 (by linarith)

/-- Positive cubes contain the origin. -/
theorem source_cube_nonempty {r : ℝ} (hr : 0 < r) :
    (originCube (d := d) r).Nonempty := by
  rw [source_originCube_eq_ball hr]
  exact ⟨0, mem_ball_self (by linarith)⟩

/-- Every literal seed simplex is an open bounded convex domain. -/
theorem source_cell_domain (cell : SeedCell d) :
    IsOpenBoundedConvexDomain (seedCellSet cell) :=
  Foundations.Simplex.isOpenBoundedConvexDomain_kuhnSimplex _ _ _

/-- Every literal seed simplex is nonempty. -/
theorem source_cell_nonempty (cell : SeedCell d) : (seedCellSet cell).Nonempty :=
  Foundations.Simplex.nonempty_kuhnSimplex _ _ _

/-- The seed cell (cube, simplex and vertex data) of an exterior cell. -/
def whitneySeedCellOfExterior {τ : ℝ} (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    SeedCell d := ⟨cell.1.1, cell.2.1, cell.2.2⟩

/-- The seed-cell center is the exterior-cell center. -/
theorem seedCellCenter_eq_statement {τ : ℝ} (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    seedCellCenter (whitneySeedCellOfExterior cell) =
      CoarseDeGiorgi.exteriorCellCenter cell := by
  rfl

/-- The seed-cell simplex is the exterior-cell set. -/
theorem seedCellSet_eq_statement {τ : ℝ} (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    seedCellSet (whitneySeedCellOfExterior cell) = CoarseDeGiorgi.exteriorCellSet cell := by
  rw [seedCellSet, CoarseDeGiorgi.exteriorCellSet,
    seedCellCenter_eq_statement, Moments.simplex_eq_kuhnSimplex]
  rfl

end CoarseDeGiorgi.Whitney

namespace CoarseDeGiorgi.Harnack.Replacement
variable {d : ℕ}

/-- The Whitney seed cell (cube, bins, order) underlying an exterior cell. -/
def whitneyCell {τ : ℝ} (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    Whitney.SeedCell d := ⟨cell.1.1, cell.2.1, cell.2.2⟩

/-- The set of an exterior cell is the set of its underlying Whitney seed cell. -/
theorem cellSet_eq_whitney {τ : ℝ} (cell : CoarseDeGiorgi.ExteriorCell d τ) :
    CoarseDeGiorgi.exteriorCellSet cell = Whitney.seedCellSet (whitneyCell cell) := by
  rw [CoarseDeGiorgi.exteriorCellSet, Whitney.seedCellSet, Moments.simplex_eq_kuhnSimplex]
  rfl

/-- Distinct exterior cells have distinct underlying Whitney seed cells. -/
theorem whitneyCell_injective {τ : ℝ} :
    Function.Injective (@whitneyCell d τ) := by
  intro x y h
  have hcube : x.1.1 = y.1.1 := congrArg Whitney.SeedCell.cube h
  have hbins : x.2.1 = y.2.1 := congrArg Whitney.SeedCell.bins h
  have horder : x.2.2 = y.2.2 := congrArg Whitney.SeedCell.order h
  apply Prod.ext
  · apply Subtype.ext
    exact hcube
  · exact Prod.ext hbins horder

end CoarseDeGiorgi.Harnack.Replacement
