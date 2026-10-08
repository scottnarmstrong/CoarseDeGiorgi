module

public import CoarseDeGiorgi.Foundations.Simplex.Partition

/-! # Nested Kuhn cells under triadic subdivision

The bins `a i ∈ Fin 3` describe the three fine intervals in each coarse
coordinate. Sorting `(bin, fine rank)` implements the nesting argument
stated after `e.simplex.family`.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Simplex

open Homogenization Set

/-- The center of the fine cube selected by its coordinate bins. -/
noncomputable def fineCubeCenter {d : ℕ} (n : ℤ) (z : Vec d) (a : Fin d → Fin 3) : Vec d :=
  fun i => z i + (3 : ℝ) ^ (n - 1) * ((a i).val - 1 : ℝ)

private theorem three_mul_fine_scale (n : ℤ) :
    3 * (3 : ℝ) ^ (n - 1) = (3 : ℝ) ^ n := by
  rw [zpow_sub_one₀ (by norm_num)]
  ring

theorem simplexCube_fineCubeCenter_subset {d : ℕ} (n : ℤ) (z : Vec d)
    (a : Fin d → Fin 3) : simplexCube (n - 1) (fineCubeCenter n z a) ⊆ simplexCube n z := by
  intro x hx i
  have hδ : 0 < (3 : ℝ) ^ (n - 1) := zpow_pos (by norm_num) _
  have hs := three_mul_fine_scale n
  have ha0 : 0 ≤ ((a i).val : ℝ) := Nat.cast_nonneg _
  have ha2 : ((a i).val : ℝ) ≤ 2 := by exact_mod_cast (show (a i).val ≤ 2 by omega)
  have hshift0 := mul_le_mul_of_nonneg_left ha0 hδ.le
  have hshift2 := mul_le_mul_of_nonneg_left ha2 hδ.le
  have hl := (hx i).1
  have hu := (hx i).2
  dsimp only [fineCubeCenter] at hl hu
  constructor <;> nlinarith only [hl, hu, hs, hshift0, hshift2]

end CoarseDeGiorgi.Foundations.Simplex
