module

public import CoarseDeGiorgi.Whitney.SeedCollar
public import CoarseDeGiorgi.Whitney.SeedInterpolation
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! # Affine formulas for the actual seed on the exterior cells -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney

open Homogenization Set

noncomputable section

variable {d : ℕ}

/-- Integer child-center index in the uniform fine grid. -/
def seedCellMeshIndex (cell : SeedCell d) : Fin d → ℤ :=
  fun i => 3 * cell.cube.index i + (cell.bins i).val - 1

def seedCellNatLevel (cell : SeedCell d) : ℕ := (seedCellLevel cell).toNat

theorem seedCellNatLevel_cast (cell : SeedCell d) (hl : 0 ≤ seedCellLevel cell) :
    (seedCellNatLevel cell : ℤ) = 1 - cell.cube.scale := Int.toNat_of_nonneg hl

theorem seedCellScale_eq_seedScale (cell : SeedCell d) (hl : 0 ≤ seedCellLevel cell) :
    seedCellScale cell = seedScale (seedCellNatLevel cell) := by
  unfold seedCellScale seedScale
  rw [seedCellNatLevel_cast cell hl]
  congr 1
  omega

theorem seedCellCenter_eq_mesh (cell : SeedCell d) (hl : 0 ≤ seedCellLevel cell) :
    seedCellCenter cell = fun i => seedScale (seedCellNatLevel cell) * (seedCellMeshIndex cell i : ℝ) := by
  funext i
  have hs := seedCellScale_parent cell
  change cubeScaleFactor cell.cube = 3 * (3 : ℝ) ^ (cell.cube.scale - 1) at hs
  unfold seedCellCenter Foundations.Simplex.fineCubeCenter triadicCenter seedCellMeshIndex
  rw [← seedCellScale_eq_seedScale cell hl]
  unfold seedCellScale
  push_cast
  rw [hs]
  ring

theorem seedCellSet_subset_parent (cell : SeedCell d) :
    seedCellSet cell ⊆ closedTriadicCube cell.cube := by
  intro x hx
  have hc := Foundations.Simplex.simplexCube_fineCubeCenter_subset cell.cube.scale
    (triadicCenter cell.cube) cell.bins hx.1
  intro i
  have hi := hc i
  change -cubeScaleFactor cell.cube / 2 < x i - triadicCenter cell.cube i ∧
    x i - triadicCenter cell.cube i < cubeScaleFactor cell.cube / 2 at hi
  apply abs_le.mpr
  constructor <;> linarith only [hi.1, hi.2]

end

end CoarseDeGiorgi.Whitney

