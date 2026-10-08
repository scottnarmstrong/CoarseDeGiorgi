import CoarseDeGiorgi.Localization.Geometry
import CoarseDeGiorgi.Statements.OriginCube
import Mathlib.Algebra.Order.Floor.Ring

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization Set
open scoped BigOperators

noncomputable section

/-- The closed centered cube of side `7/8`. -/
def closedSevenEighthsCube {d : ℕ} : Set (Vec d) :=
  {x | ∀ i, |x i| ≤ (7 / 16 : ℝ)}

/-- The dimension-only lattice box used at the fixed scale `m=4`. -/
def fixedLogGrid {d : ℕ} : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-35 : ℤ) 35)

private theorem gridSpacing_four : Localization.gridSpacing 4 = (1 / 81 : ℝ) := by
  rw [Localization.gridSpacing]
  norm_num

private theorem fixedLogGrid_mem {d : ℕ} {z : Fin d → ℤ}
    (hz : z ∈ fixedLogGrid) : ∀ i, -35 ≤ z i ∧ z i ≤ 35 := by
  have hz' := Fintype.mem_piFinset.mp hz
  intro i
  exact Finset.mem_Icc.mp (hz' i)

private theorem fixedLogGrid_center_bound {d : ℕ} {z : Fin d → ℤ}
    (hz : z ∈ fixedLogGrid) (i : Fin d) :
    |Localization.gridCenter 4 z i| ≤ (7 / 16 : ℝ) := by
  have hz' := fixedLogGrid_mem hz i
  rw [Localization.gridCenter, gridSpacing_four]
  have hzlo : (-35 : ℝ) ≤ (z i : ℝ) := by exact_mod_cast hz'.1
  have hzhi : (z i : ℝ) ≤ 35 := by exact_mod_cast hz'.2
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 81)]
  have hzabs : |(z i : ℝ)| ≤ 35 := abs_le.mpr ⟨hzlo, hzhi⟩
  calc
    |(z i : ℝ)| * (1 / 81) ≤ 35 * (1 / 81) :=
      mul_le_mul_of_nonneg_right hzabs (by norm_num)
    _ ≤ 7 / 16 := by norm_num

private theorem fixedLogGrid_nearest_mem {d : ℕ} {x : Vec d}
    (hx : x ∈ closedSevenEighthsCube) :
    Localization.nearestGrid 4 x ∈ fixedLogGrid := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have hxcoord := abs_le.mp (hx i)
  have hs := gridSpacing_four
  have hdiv : x i / Localization.gridSpacing 4 = 81 * x i := by
    rw [hs]
    norm_num
    ring
  have hlo : (-35 : ℝ) ≤ x i / Localization.gridSpacing 4 + 1 / 2 := by
    rw [hdiv]
    nlinarith [hxcoord.1]
  have hhi : x i / Localization.gridSpacing 4 + 1 / 2 < 36 := by
    rw [hdiv]
    nlinarith [hxcoord.2]
  constructor
  · change (-35 : ℤ) ≤ ⌊x i / Localization.gridSpacing 4 + 1 / 2⌋
    exact Int.le_floor.mpr (by exact_mod_cast hlo)
  · change ⌊x i / Localization.gridSpacing 4 + 1 / 2⌋ ≤ (35 : ℤ)
    exact Int.floor_le_iff.mpr (by norm_num at hhi ⊢; exact hhi)

/-- The closed cube `closedSevenEighthsCube` is covered by the level-`4` auxiliary cubes
indexed by `fixedLogGrid`. -/
theorem fixedLogGrid_cover {d : ℕ} :
    (closedSevenEighthsCube (d := d) : Set (Vec d)) ⊆
      ⋃ z ∈ (fixedLogGrid (d := d) : Finset (Fin d → ℤ)), auxCube 4 z := by
  intro x hx
  let z := Localization.nearestGrid 4 x
  have hz : z ∈ fixedLogGrid := fixedLogGrid_nearest_mem hx
  have hcentral : x ∈ Localization.centralCube 4 z := by
    exact Localization.mem_centralCube_nearestGrid 4 x
  exact Set.mem_iUnion₂.mpr ⟨z, hz,
    Localization.centralCube_subset_auxCube 4 z hcentral⟩

private theorem closedAuxCube_isClosed {d : ℕ} (z : Fin d → ℤ) :
    IsClosed (Localization.closedAuxCube 4 z) := by
  unfold Localization.closedAuxCube Localization.gridCenter Localization.gridSpacing
  simp only [ofPred_forall]
  exact isClosed_iInter fun i =>
    isClosed_le ((continuous_apply i).sub continuous_const).abs continuous_const

private theorem fixedLogGrid_center_meets {d : ℕ} {z : Fin d → ℤ}
    (hz : z ∈ fixedLogGrid) :
    ∃ y ∈ closedSevenEighthsCube, y ∈ Localization.centralCube 4 z := by
  refine ⟨Localization.gridCenter 4 z, ?_, ?_⟩
  · intro i
    exact fixedLogGrid_center_bound hz i
  · intro i
    change |Localization.gridCenter 4 z i - Localization.gridCenter 4 z i| ≤
      Localization.gridSpacing 4 / 2
    simp only [sub_self, abs_zero]
    exact div_nonneg (Localization.gridSpacing_pos 4).le (by norm_num)

private theorem closedLogCube_radius_bound {d : ℕ} {y : Vec d}
    (hy : y ∈ (closedSevenEighthsCube (d := d) : Set (Vec d))) :
    ∀ i, |y i| ≤ (7 / 8 : ℝ) / 2 := by
  have hy' : ∀ i, |y i| ≤ (7 / 16 : ℝ) := hy
  simpa only [show (7 / 8 : ℝ) / 2 = 7 / 16 by ring] using hy'

/-- Every selected cube has its closure strictly inside the `15/16` cube. -/
theorem fixedLogGrid_closure_inside {d : ℕ} {z : Fin d → ℤ}
    (hz : z ∈ fixedLogGrid) :
    closure (auxCube 4 z) ⊆ originCube (d := d) (15 / 16 : ℝ) := by
  have hK : ∀ y ∈ (closedSevenEighthsCube (d := d) : Set (Vec d)),
      ∀ i, |y i| ≤ (7 / 8 : ℝ) / 2 :=
    by intro y hy i; exact closedLogCube_radius_bound hy i
  have hmargin : (7 / 8 : ℝ) + 4 * Localization.gridSpacing 4 < 15 / 16 := by
    rw [gridSpacing_four]
    norm_num
  have hcontain := Localization.closedAuxCube_subset_radiusCube_of_meets
    (m := 4) (z := z) hK hmargin (fixedLogGrid_center_meets hz)
  have hclosure : closure (auxCube 4 z) ⊆ Localization.closedAuxCube 4 z :=
    closure_minimal (Localization.auxCube_subset_closedAuxCube 4 z)
      (closedAuxCube_isClosed z)
  intro x hx i
  have hx' := hcontain (hclosure hx) i
  simpa [Localization.radiusCube, originCube, abs_lt] using hx'

end

end CoarseDeGiorgi.Harnack.Log
