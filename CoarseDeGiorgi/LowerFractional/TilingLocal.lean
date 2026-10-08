import CoarseDeGiorgi.LowerFractional.Aliases
import CoarseDeGiorgi.Foundations.Simplex.Partition

/-! A threefold cube is tiled by its 3^d child cubes and their Kuhn simplices.
The local indexing is a concrete witness, not another copy of the `Statements/` cells. -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

abbrev LowerChildIndex (d : ℕ) := (Fin d → Fin 3) × Equiv.Perm (Fin d)

def lowerChildGrid {d : ℕ} (c : Fin d → ℤ) (η : LowerChildIndex d) :
    (Fin d → ℤ) × Equiv.Perm (Fin d) :=
  (fun i => c i + ((η.1 i : ℤ) - 1), η.2)

def lowerChildCenter {d : ℕ} (k : ℤ) (c : Fin d → ℤ) (j : Fin d → Fin 3) : Vec d :=
  fun i => (3 : ℝ) ^ (-k) * ((c i : ℝ) + ((j i : ℝ) - 1))

def lowerChildCell {d : ℕ} (k : ℤ) (c : Fin d → ℤ) (η : LowerChildIndex d) : Set (Vec d) :=
  Aliases.simplex (-k) η.2 (lowerChildCenter k c η.1)

lemma lower_aux_side (k : ℤ) : (3 : ℝ) ^ (1 - k) = 3 * (3 : ℝ) ^ (-k) := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]

/-- Coordinate hyperplanes are null, including arbitrary translates. -/
lemma lower_coordinate_ne_ae {d : ℕ} (i : Fin d) (t : ℝ) :
    ∀ᵐ x : Vec d ∂volume, x i ≠ t := by
  let L : Vec d →ₗ[ℝ] ℝ := LinearMap.proj i
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro he
    have hp : Pi.single i (1 : ℝ) ∈ LinearMap.ker L := by rw [he]; exact Submodule.mem_top
    norm_num only [LinearMap.mem_ker, L, LinearMap.proj_apply, Pi.single_eq_same] at hp
  have hn := Measure.addHaar_submodule volume (LinearMap.ker L) hker
  apply ae_iff.mpr
  have hs : {x : Vec d | ¬ x i ≠ t} =
      (fun x : Vec d => x + -Pi.single i t) ⁻¹' (LinearMap.ker L : Set (Vec d)) := by
    ext x
    change (¬ x i ≠ t) ↔ (x + -(Pi.single i t : Vec d)) i = 0
    simp only [not_not, Pi.add_apply, Pi.neg_apply, Pi.single_eq_same,
      ← sub_eq_add_neg, sub_eq_zero]
  rw [hs, measure_preimage_add_right]
  exact hn

lemma lower_child_cube_subset {d : ℕ} (k : ℤ) (c : Fin d → ℤ) (j : Fin d → Fin 3) :
    Foundations.Simplex.simplexCube (-k) (lowerChildCenter k c j) ⊆ auxCube k c := by
  have hh : 0 < (3 : ℝ) ^ (-k) := zpow_pos (by norm_num) _
  intro x hx i
  have hj0 : (0 : ℝ) ≤ (j i : ℝ) := Nat.cast_nonneg _
  have hj2 : (j i : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ (j i).isLt
  have hi := hx i
  change -(3 : ℝ) ^ (-k) / 2 < x i -
      (3 : ℝ) ^ (-k) * ((c i : ℝ) + ((j i : ℝ) - 1)) ∧
    x i - (3 : ℝ) ^ (-k) * ((c i : ℝ) + ((j i : ℝ) - 1)) < (3 : ℝ) ^ (-k) / 2 at hi
  change |x i - (c i : ℝ) * (3 : ℝ) ^ (-k)| < (3 : ℝ) ^ (1 - k) / 2
  rw [lower_aux_side, abs_lt]
  have hlo := mul_le_mul_of_nonneg_left hj0 hh.le
  have hhi := mul_le_mul_of_nonneg_left hj2 hh.le
  constructor <;> linarith only [hi.1, hi.2, hlo, hhi]

lemma lower_child_cubes_pairwiseDisjoint {d : ℕ} (k : ℤ) (c : Fin d → ℤ) :
    Pairwise (fun j v : Fin d → Fin 3 => Disjoint
      (Foundations.Simplex.simplexCube (-k) (lowerChildCenter k c j))
      (Foundations.Simplex.simplexCube (-k) (lowerChildCenter k c v))) := by
  intro j v hjv
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hjv
  funext i
  apply Fin.ext
  have hh : 0 < (3 : ℝ) ^ (-k) := zpow_pos (by norm_num) _
  have hxi := hx i
  have hyi := hy i
  change -(3 : ℝ) ^ (-k) / 2 < x i -
      (3 : ℝ) ^ (-k) * ((c i : ℝ) + ((j i : ℝ) - 1)) ∧
    x i - (3 : ℝ) ^ (-k) * ((c i : ℝ) + ((j i : ℝ) - 1)) < (3 : ℝ) ^ (-k) / 2 at hxi
  change -(3 : ℝ) ^ (-k) / 2 < x i -
      (3 : ℝ) ^ (-k) * ((c i : ℝ) + ((v i : ℝ) - 1)) ∧
    x i - (3 : ℝ) ^ (-k) * ((c i : ℝ) + ((v i : ℝ) - 1)) < (3 : ℝ) ^ (-k) / 2 at hyi
  have hlt : (j i : ℝ) < (v i : ℝ) + 1 := by nlinarith only [hxi.1, hyi.2, hh]
  have hgt : (v i : ℝ) < (j i : ℝ) + 1 := by nlinarith only [hyi.1, hxi.2, hh]
  have hl : (j i).val < (v i).val + 1 := by exact_mod_cast hlt
  have hg : (v i).val < (j i).val + 1 := by exact_mod_cast hgt
  omega

lemma lower_child_cubes_ae_cover {d : ℕ} (k : ℤ) (c : Fin d → ℤ) :
    (⋃ j : Fin d → Fin 3, Foundations.Simplex.simplexCube (-k) (lowerChildCenter k c j))
      =ᵐ[volume] auxCube k c := by
  have hh : 0 < (3 : ℝ) ^ (-k) := zpow_pos (by norm_num) _
  have hf : ∀ᵐ x : Vec d ∂volume, ∀ i : Fin d,
      x i ≠ (c i : ℝ) * (3 : ℝ) ^ (-k) - (3 : ℝ) ^ (-k) / 2 ∧
      x i ≠ (c i : ℝ) * (3 : ℝ) ^ (-k) + (3 : ℝ) ^ (-k) / 2 :=
    ae_all_iff.mpr fun i => (lower_coordinate_ne_ae i _).and (lower_coordinate_ne_ae i _)
  filter_upwards [hf] with x hx
  apply propext
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact lower_child_cube_subset k c j hj
  · intro hQ
    let j : Fin d → Fin 3 := fun i =>
      if x i < (c i : ℝ) * (3 : ℝ) ^ (-k) - (3 : ℝ) ^ (-k) / 2 then 0
      else if x i < (c i : ℝ) * (3 : ℝ) ^ (-k) + (3 : ℝ) ^ (-k) / 2 then 1 else 2
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    intro i
    have hi := hQ i
    change |x i - (c i : ℝ) * (3 : ℝ) ^ (-k)| < (3 : ℝ) ^ (1 - k) / 2 at hi
    rw [lower_aux_side, abs_lt] at hi
    change -(3 : ℝ) ^ (-k) / 2 < x i - lowerChildCenter k c j i ∧
      x i - lowerChildCenter k c j i < (3 : ℝ) ^ (-k) / 2
    dsimp [lowerChildCenter, j]
    split_ifs with hlo hhi
    · norm_num only [Fin.val_zero, Nat.cast_zero]
      constructor <;> linarith only [hi.1, hlo]
    · norm_num only [Fin.val_one, Nat.cast_one]
      simp only [add_zero]
      have hlo' := lt_of_le_of_ne (le_of_not_gt hlo) (hx i).1.symm
      constructor <;> linarith only [hlo', hhi]
    · norm_num only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_ofNat]
      change -(3 : ℝ) ^ (-k) / 2 < x i - (3 : ℝ) ^ (-k) * ((c i : ℝ) + 1) ∧
        x i - (3 : ℝ) ^ (-k) * ((c i : ℝ) + 1) < (3 : ℝ) ^ (-k) / 2
      have hhi' := lt_of_le_of_ne (le_of_not_gt hhi) (hx i).2.symm
      constructor <;> linarith only [hhi', hi.2]

/-- The local child index family has exactly the cardinality `3^d d!`. -/
lemma lower_child_index_card (d : ℕ) : Fintype.card (LowerChildIndex d) = 3 ^ d * d.factorial := by
  simp only [LowerChildIndex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_perm]

lemma lower_child_grid_injective {d : ℕ} (c : Fin d → ℤ) : Function.Injective (lowerChildGrid c) := by
  intro η ξ h
  apply Prod.ext
  · funext i
    apply Fin.ext
    have hi := congrFun (congrArg Prod.fst h) i
    change c i + ((η.1 i : ℤ) - 1) = c i + ((ξ.1 i : ℤ) - 1) at hi
    exact_mod_cast (show (η.1 i : ℤ) = (ξ.1 i : ℤ) by omega)
  · exact congrArg (fun p : (Fin d → ℤ) × Equiv.Perm (Fin d) => p.2) h

lemma lower_simplex_eq_kuhn {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    Aliases.simplex n π z = Foundations.Simplex.kuhnSimplex n π z :=
  Moments.simplex_eq_kuhnSimplex n π z

lemma lower_child_cell_subset {d : ℕ} (k : ℤ) (c : Fin d → ℤ) (η : LowerChildIndex d) :
    lowerChildCell k c η ⊆ auxCube k c := by
  unfold lowerChildCell
  rw [lower_simplex_eq_kuhn]
  exact (Foundations.Simplex.kuhnSimplex_subset_cube _ _ _).trans
    (lower_child_cube_subset k c η.1)

lemma lower_child_cells_pairwiseDisjoint {d : ℕ} (k : ℤ) (c : Fin d → ℤ) :
    Pairwise (fun η ξ : LowerChildIndex d => Disjoint (lowerChildCell k c η) (lowerChildCell k c ξ)) := by
  intro η ξ hne
  unfold lowerChildCell
  rw [lower_simplex_eq_kuhn, lower_simplex_eq_kuhn]
  by_cases hj : η.1 = ξ.1
  · have hp : η.2 ≠ ξ.2 := fun hp => hne (Prod.ext hj hp)
    rw [hj]
    exact Foundations.Simplex.pairwise_disjoint_kuhnSimplex _ _ hp
  · exact (lower_child_cubes_pairwiseDisjoint k c hj).mono
      (Foundations.Simplex.kuhnSimplex_subset_cube _ _ _)
      (Foundations.Simplex.kuhnSimplex_subset_cube _ _ _)

lemma lower_child_cells_ae_cover {d : ℕ} (k : ℤ) (c : Fin d → ℤ) :
    (⋃ η : LowerChildIndex d, lowerChildCell k c η) =ᵐ[volume] auxCube k c := by
  have hs : ∀ᵐ x : Vec d ∂volume, ∀ j : Fin d → Fin 3,
      x ∈ (⋃ π : Equiv.Perm (Fin d), Foundations.Simplex.kuhnSimplex (-k) π
        (lowerChildCenter k c j)) ↔
      x ∈ Foundations.Simplex.simplexCube (-k) (lowerChildCenter k c j) :=
    ae_all_iff.mpr fun j =>
      (Foundations.Simplex.iUnion_kuhnSimplex_ae_eq_cube (-k) (lowerChildCenter k c j)).mono
        fun _ h => Iff.of_eq h
  filter_upwards [hs, lower_child_cubes_ae_cover k c] with x hx hc
  apply propext
  rw [Set.mem_iUnion]
  rw [← Iff.of_eq hc]
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨⟨j, π⟩, hp⟩
    apply Exists.intro j
    apply (hx j).mp
    exact Set.mem_iUnion.mpr ⟨π, (lower_simplex_eq_kuhn _ _ _) ▸ hp⟩
  · rintro ⟨j, hj⟩
    obtain ⟨π, hp⟩ := Set.mem_iUnion.mp ((hx j).mpr hj)
    refine ⟨(j, π), ?_⟩
    change x ∈ Aliases.simplex (-k) π (lowerChildCenter k c j)
    rw [lower_simplex_eq_kuhn]
    exact hp


end

end CoarseDeGiorgi.LowerFractional
