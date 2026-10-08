import CoarseDeGiorgi.Whitney.SourceWitnessResponse
import CoarseDeGiorgi.Whitney.SourceWitnessCore
import CoarseDeGiorgi.Foundations.Simplex.Partition
import CoarseDeGiorgi.Statements.WhitneyCubesProperties

/-! # Canonical active seed cells and their finite layers -/
namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set
noncomputable section
variable {d : ℕ}

/-- Level, mesh center and permutation determine an actual seed cell. -/
theorem source_seedCell_code_injective :
    Function.Injective (fun cell : SeedCell d =>
      (seedCellLevel cell, seedCellMeshIndex cell, cell.order)) := by
  intro c b he
  have hlevel := congrArg Prod.fst he
  have hmesh := congrArg (fun x => x.2.1) he
  have horder := congrArg (fun x => x.2.2) he
  have hscale : c.cube.scale = b.cube.scale := by
    change 1 - c.cube.scale = 1 - b.cube.scale at hlevel
    omega
  have hbins : c.bins = b.bins := by
    funext i
    apply Fin.ext
    have hm := congrFun hmesh i
    change 3 * c.cube.index i + (c.bins i).val - 1 =
      3 * b.cube.index i + (b.bins i).val - 1 at hm
    have hc := (c.bins i).isLt
    have hb := (b.bins i).isLt
    omega
  have hidx : c.cube.index = b.cube.index := by
    funext i
    have hm := congrFun hmesh i
    change 3 * c.cube.index i + (c.bins i).val - 1 =
      3 * b.cube.index i + (b.bins i).val - 1 at hm
    rw [hbins] at hm
    omega
  cases c with
  | mk c cb co =>
    cases b with
    | mk b bb bo =>
      cases c
      cases b
      simp_all only

/-- The actual seed-cell carrier is countable. -/
instance source_seedCell_countable : Countable (SeedCell d) :=
  source_seedCell_code_injective.countable

/-- A child open simplex is contained in its parent's open cube. -/
theorem source_seedCell_subset_open_parent (cell : SeedCell d) :
    seedCellSet cell ⊆ openCubeSet cell.cube := by
  intro x hx
  have hb := Foundations.Simplex.simplexCube_fineCubeCenter_subset
    cell.cube.scale (triadicCenter cell.cube) cell.bins hx.1
  intro i
  have hi := hb i
  dsimp [triadicCenter, cubeScaleFactor] at hi ⊢
  constructor <;> nlinarith only [hi.1, hi.2]

/-- Cells with the same parent have disjoint interiors unless their child and
permutation data agree. -/
theorem source_seedCells_same_parent_disjoint {c b : SeedCell d}
    (hparent : c.cube = b.cube) (hne : c ≠ b) :
    Disjoint (seedCellSet c) (seedCellSet b) := by
  by_cases hbins : c.bins = b.bins
  · have horder : c.order ≠ b.order := by
      intro ho
      apply hne
      cases c
      cases b
      simp_all only
    have hcenter : seedCellCenter c = seedCellCenter b := by
      unfold seedCellCenter
      rw [hparent, hbins]
    unfold seedCellSet
    rw [hparent, hcenter]
    exact Foundations.Simplex.pairwise_disjoint_kuhnSimplex _ _ horder
  · apply disjoint_left.mpr
    intro x hx hy
    apply hbins
    funext i
    apply Fin.ext
    have hxi := hx.1 i
    have hyi := hy.1 i
    have hs : 0 < (3 : ℝ) ^ (c.cube.scale - 1) := zpow_pos (by norm_num) _
    change -(3 : ℝ) ^ (c.cube.scale - 1) / 2 <
      x i - (triadicCenter c.cube i + (3 : ℝ) ^ (c.cube.scale - 1) * ((c.bins i).val - 1)) ∧
      x i - (triadicCenter c.cube i + (3 : ℝ) ^ (c.cube.scale - 1) * ((c.bins i).val - 1)) <
        (3 : ℝ) ^ (c.cube.scale - 1) / 2 at hxi
    change -(3 : ℝ) ^ (b.cube.scale - 1) / 2 <
      x i - (triadicCenter b.cube i + (3 : ℝ) ^ (b.cube.scale - 1) * ((b.bins i).val - 1)) ∧
      x i - (triadicCenter b.cube i + (3 : ℝ) ^ (b.cube.scale - 1) * ((b.bins i).val - 1)) <
        (3 : ℝ) ^ (b.cube.scale - 1) / 2 at hyi
    rw [← hparent] at hyi
    apply le_antisymm
    · by_contra hn
      have hnR : ((b.bins i).val : ℝ) + 1 ≤ (c.bins i).val := by exact_mod_cast (by omega : (b.bins i).val + 1 ≤ (c.bins i).val)
      nlinarith only [hxi.1, hyi.2, hs, hnR]
    · by_contra hn
      have hnR : ((c.bins i).val : ℝ) + 1 ≤ (b.bins i).val := by exact_mod_cast (by omega : (c.bins i).val + 1 ≤ (b.bins i).val)
      nlinarith only [hyi.1, hxi.2, hs, hnR]

end
end CoarseDeGiorgi.Whitney
