module

public import CoarseDeGiorgi.Whitney.SeedRefinement
public import Mathlib.Topology.Algebra.Support
public import CoarseDeGiorgi.Foundations.Triadic.WhitneyCubesProof
public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.SurfaceMeasure
public import CoarseDeGiorgi.Statements.EuclidDist
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Exterior cells of the selected Whitney cubes

The coordinate projection onto the closed reference cube, and the exterior cells (the child Kuhn
simplices of the selected Whitney cubes) with their centers, side lengths and levels.
-/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- Coordinate projection onto the closed reference cube. -/
def seedProjection (τ : ℝ) (x : Vec d) : Vec d :=
  fun i => max (-τ / 2) (min (x i) (τ / 2))

theorem seedProjection_coordinate_bound {τ : ℝ} (hτ : 0 ≤ τ) (x : Vec d) (i : Fin d) :
    |seedProjection τ x i| ≤ τ / 2 := by
  change |max (-τ / 2) (min (x i) (τ / 2))| ≤ τ / 2
  apply abs_le.mpr
  constructor
  · simpa only [neg_div] using le_max_left (-τ / 2) (min (x i) (τ / 2))
  · exact max_le (by linarith only [hτ]) (min_le_right _ _)

/-- A child Kuhn simplex of a selected cube; activity is a separate predicate. -/
structure SeedCell (d : ℕ) where
  cube : TriadicCube d
  bins : Fin d → Fin 3
  order : Equiv.Perm (Fin d)

/-- The center of the child cube carrying an exterior cell. -/
def seedCellCenter (cell : SeedCell d) : Vec d :=
  Foundations.Simplex.fineCubeCenter cell.cube.scale (triadicCenter cell.cube) cell.bins

/-- Side length of the child cube, rather than the selected parent. -/
def seedCellScale (cell : SeedCell d) : ℝ := (3 : ℝ) ^ (cell.cube.scale - 1)

/-- Exterior cell of `e.whitney.simplex.size`. -/
def seedCellSet (cell : SeedCell d) : Set (Vec d) :=
  Foundations.Simplex.kuhnSimplex (cell.cube.scale - 1) cell.order (seedCellCenter cell)

/-- Integer level; activity will force the nonnegative levels used in the source. -/
def seedCellLevel (cell : SeedCell d) : ℤ := 1 - cell.cube.scale

end

end CoarseDeGiorgi.Whitney

