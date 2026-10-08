import CoarseDeGiorgi.Whitney.SourceWitnessCells
import CoarseDeGiorgi.Whitney.SeedClosedCover
import CoarseDeGiorgi.Whitney.SeedAverage
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Data.Fintype.BigOperators
import CoarseDeGiorgi.Whitney.LiftIdentification
import CoarseDeGiorgi.Weighted.TestingCompactSupport
import CoarseDeGiorgi.Weighted.Truncation.Energy
import Mathlib.Analysis.Convex.Measure
import CoarseDeGiorgi.Statements.WhitneyCubesProperties

/-! # The actual seed vanishes off the active cell interiors -/
namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Filter Topology
noncomputable section
variable {d : ℕ}

/-- Simultaneously discard every seed simplex face, a countable null union. -/
theorem source_seed_cells_ae_interior :
    ∀ᵐ x : Vec d ∂volume, ∀ cell : SeedCell d,
      x ∈ closure (seedCellSet cell) → x ∈ seedCellSet cell := by
  apply ae_all_iff.mpr
  intro cell
  have hU := Foundations.Simplex.isOpenBoundedConvexDomain_kuhnSimplex
    (cell.cube.scale - 1) cell.order (seedCellCenter cell)
  change IsOpenBoundedConvexDomain (seedCellSet cell) at hU
  have hn := hU.convex.addHaar_frontier volume
  have hae : ∀ᵐ x ∂volume, x ∉ frontier (seedCellSet cell) := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hn
  filter_upwards [hae] with x hx
  intro hc
  by_contra hu
  apply hx
  rw [frontier, hU.isOpen.interior_eq]
  exact ⟨hc, hu⟩

/-- The open reference cube is the ball for the ambient supremum norm. -/
theorem source_originCube_eq_ball {r : ℝ} (hr : 0 < r) :
    originCube (d := d) r = Metric.ball (0 : Vec d) (r / 2) := by
  ext x
  simp only [originCube, mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
    pi_norm_lt_iff (by linarith : 0 < r / 2), Real.norm_eq_abs, abs_lt]

end
end CoarseDeGiorgi.Whitney
