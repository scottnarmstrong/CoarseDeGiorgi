import CoarseDeGiorgi.Whitney.SeedCellAffine
import CoarseDeGiorgi.Whitney.LiftSurfaceLayer
import CoarseDeGiorgi.Selection.CommonRadius
import Mathlib.Analysis.Normed.Module.RCLike.Real
import CoarseDeGiorgi.Selection.SourceResponses
import CoarseDeGiorgi.Weighted.LowerSpecNorm
import CoarseDeGiorgi.Statements.UpperResponseSpec

/-! # Actual seed cells in the response sampling grid -/
namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d : ℕ}

private theorem source_mem_triangulation_iff (j : ℕ)
    (η : (Fin d → ℤ) × Equiv.Perm (Fin d)) :
    η ∈ triangulation j ↔
      ∃ jp : (Fin d → Fin (3 ^ j)) × Equiv.Perm (Fin d),
        (gridOffset j jp.1, jp.2) = η := by
  simp only [CoarseDeGiorgi.triangulation, Finset.mem_image, Finset.mem_univ, true_and]

/-- An integer center strictly inside the centered unit grid has a `triangulation`
index. -/
theorem source_mesh_mem_triangulation (j : ℕ) (m : Fin d → ℤ)
    (π : Equiv.Perm (Fin d))
    (hm : ∀ i, |(m i : ℝ)| < ((3 ^ j : ℕ) : ℝ) / 2) :
    (m, π) ∈ triangulation j := by
  classical
  have hodd : Odd (3 ^ j : ℕ) := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow
  obtain ⟨r, hr⟩ := hodd
  have hhalf : (3 ^ j - 1) / 2 = r := by omega
  have hb (i : Fin d) : -(r : ℤ) ≤ m i ∧ m i ≤ (r : ℤ) := by
    have hlo : -((3 ^ j : ℕ) : ℝ) < (2 : ℝ) * (m i : ℝ) := by
      have hh := (abs_lt.mp (hm i)).1
      linarith only [hh]
    have hhi : (2 : ℝ) * (m i : ℝ) < ((3 ^ j : ℕ) : ℝ) := by
      have hh := (abs_lt.mp (hm i)).2
      linarith only [hh]
    have hloZ : -(3 ^ j : ℤ) < 2 * m i := by exact_mod_cast hlo
    have hhiZ : 2 * m i < (3 ^ j : ℤ) := by exact_mod_cast hhi
    have hrZ : (3 ^ j : ℤ) = 2 * (r : ℤ) + 1 := by exact_mod_cast hr
    omega
  let bins : Fin d → Fin (3 ^ j) := fun i =>
    ⟨(m i + r).toNat, by
      have hi := hb i
      have hn : 0 ≤ m i + (r : ℤ) := by omega
      have he := Int.toNat_of_nonneg hn
      omega⟩
  apply (source_mem_triangulation_iff j (m, π)).2
  refine ⟨(bins, π), ?_⟩
  apply Prod.ext
  · funext i
    change (((m i + r).toNat : ℤ) - (((3 ^ j - 1) / 2 : ℕ) : ℤ)) = m i
    rw [hhalf, Int.toNat_of_nonneg (by have := (hb i).1; omega)]
    omega
  · rfl

/-- Child centers lie in their selected parent cube. -/
theorem source_seedCellCenter_mem_parent (cell : SeedCell d) :
    seedCellCenter cell ∈ closedTriadicCube cell.cube := by
  intro i
  have hs : 0 < seedCellScale cell := zpow_pos (by norm_num) _
  have hb : (0 : ℝ) ≤ (cell.bins i).val := Nat.cast_nonneg _
  have ht : ((cell.bins i).val : ℝ) ≤ 2 := by exact_mod_cast (by omega : (cell.bins i).val ≤ 2)
  change |triadicCenter cell.cube i + seedCellScale cell *
    ((cell.bins i).val - 1) - triadicCenter cell.cube i| ≤ cubeScaleFactor cell.cube / 2
  rw [seedCellScale_parent]
  apply abs_le.mpr
  constructor <;> nlinarith only [hs, hb, ht]

end
end CoarseDeGiorgi.Whitney
