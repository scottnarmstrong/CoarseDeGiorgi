import CoarseDeGiorgi.Moments.Cells
import CoarseDeGiorgi.Foundations.Simplex.Partition
import CoarseDeGiorgi.Statements.BesovCubeNorm

/-! # Triadic cubes and the simplices they contain

The cube `cubeSet k j = z + □_{-k}`, `z = 3^{-k} gridOffset k j`, of the quasi-norm `besovCubeNorm`
is the open cube of side `3^{-k}` about `z`; it contains each of its `d!` simplices, which have equal
volume, and lies in the unit cube. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.CoefficientConditions

/-- The centre `3^{-k} • gridOffset k j`. -/
noncomputable def cubeCentre {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Vec d :=
  fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)

/-- The cube `z + □_{-k}` of `besovCubeNorm`. -/
def cubeSet {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) : Set (Vec d) :=
  {x : Vec d | x - (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ)) ∈
    originCube ((3 : ℝ) ^ (-(k : ℤ)))}

theorem cubeSet_eq {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    cubeSet k j = Foundations.Simplex.simplexCube (-(k : ℤ)) (cubeCentre k j) := by
  ext x
  simp only [cubeSet, cubeCentre, originCube, Foundations.Simplex.simplexCube, Set.mem_ofPred_eq,
    Pi.sub_apply]
  refine forall_congr' (fun i => ?_)
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The simplex of `π` in the cube of centre `3^{-k} gridOffset k j`. -/
def cellSet {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) : Set (Vec d) :=
  CoarseDeGiorgi.simplex (-(k : ℤ)) π (cubeCentre k j)

theorem cellSet_subset {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) :
    cellSet k j π ⊆ cubeSet k j := by
  unfold cellSet
  rw [Moments.simplex_eq_kuhnSimplex, cubeSet_eq]
  exact Foundations.Simplex.kuhnSimplex_subset_cube _ _ _

theorem volume_cubeSet_eq {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) (π : Equiv.Perm (Fin d)) :
    volume (cubeSet k j) = (d.factorial : ℝ≥0∞) * volume (cellSet k j π) := by
  unfold cellSet
  rw [Moments.simplex_eq_kuhnSimplex, cubeSet_eq, Foundations.Simplex.volume_simplexCube,
    Foundations.Simplex.factorial_mul_volume_kuhnSimplex]

theorem volume_cellSet_ne_zero {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k))
    (π : Equiv.Perm (Fin d)) : volume (cellSet k j π) ≠ 0 := by
  unfold cellSet
  rw [Moments.simplex_eq_kuhnSimplex, Foundations.Simplex.volume_kuhnSimplex]
  have : (0 : ℝ) < (3 : ℝ) ^ ((-(k : ℤ)) * (d : ℤ)) := zpow_pos (by norm_num) _
  refine (ENNReal.div_pos (by simpa using this) (by simp)).ne'

theorem volume_cellSet_ne_top {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k))
    (π : Equiv.Perm (Fin d)) : volume (cellSet k j π) ≠ ⊤ := by
  unfold cellSet
  rw [Moments.simplex_eq_kuhnSimplex, Foundations.Simplex.volume_kuhnSimplex]
  exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by exact_mod_cast Nat.factorial_ne_zero d)

private theorem grid_half_width' (k : ℕ) :
    3 ^ k = 2 * ((3 ^ k - 1) / 2) + 1 := by
  have hodd : Odd (3 ^ k : ℕ) := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow
  obtain ⟨t, ht⟩ := hodd
  omega

theorem cubeSet_subset_originCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    cubeSet k j ⊆ originCube 1 := by
  have hs : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ (-(k : ℤ)) * (3 ^ k : ℕ) = 1 := by
    simp only [zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  have hhalfR : ((3 ^ k : ℕ) : ℝ) = 2 * (((3 ^ k - 1) / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast grid_half_width' k
  intro x hx i
  have hxi := hx i
  simp only [Pi.sub_apply] at hxi
  have hj0 : (0 : ℝ) ≤ (j i).val := Nat.cast_nonneg _
  have hjhi : ((j i).val : ℝ) ≤ (3 ^ k : ℕ) - 1 := by
    have h : (j i).val + 1 ≤ 3 ^ k := Nat.succ_le_of_lt (j i).isLt
    have hR : ((j i).val : ℝ) + 1 ≤ (3 ^ k : ℕ) := by exact_mod_cast h
    linarith only [hR]
  have hshift0 := mul_nonneg hs.le hj0
  have hshifthi := mul_le_mul_of_nonneg_left hjhi hs.le
  have hmid : (3 : ℝ) ^ (-(k : ℤ)) *
      (((3 ^ k - 1) / 2 : ℕ) : ℝ) = (1 - (3 : ℝ) ^ (-(k : ℤ))) / 2 := by
    nlinarith only [hhalfR, hscale]
  simp only [CoarseDeGiorgi.gridOffset, Int.cast_sub, Int.cast_natCast] at hxi
  constructor <;> nlinarith only [hxi.1, hxi.2, hshift0, hshifthi, hmid, hscale]

end CoarseDeGiorgi.CoefficientConditions
