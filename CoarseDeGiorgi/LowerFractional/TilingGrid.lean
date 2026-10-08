module

public import CoarseDeGiorgi.LowerFractional.TilingLocal
public import CoarseDeGiorgi.Statements.AuxDescendantCube

/-! Embedding the concrete local tiling into the audited global triangulation. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Set Aliases
open scoped BigOperators

noncomputable section

lemma lower_grid_half_width (k : ℕ) : 3 ^ k = 2 * ((3 ^ k - 1) / 2) + 1 := by
  obtain ⟨t, ht⟩ := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow (n := k)
  omega

lemma lower_mem_triangulation_iff {d : ℕ} (k : ℕ) (v : Fin d → ℤ) (π : Equiv.Perm (Fin d)) :
    (v, π) ∈ triangulation k ↔
      ∀ i, -(((3 ^ k - 1) / 2 : ℕ) : ℤ) ≤ v i ∧
        v i ≤ (((3 ^ k - 1) / 2 : ℕ) : ℤ) := by
  classical
  let N : ℤ := ((3 ^ k - 1) / 2 : ℕ)
  have hN : (3 ^ k : ℕ) = 2 * ((3 ^ k - 1) / 2) + 1 := lower_grid_half_width k
  unfold triangulation
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨j, τ⟩, _, he⟩ i
    have hi := congrFun (congrArg Prod.fst he) i
    change (j i : ℤ) - N = v i at hi
    have hj0 : (0 : ℤ) ≤ (j i : ℤ) := by exact_mod_cast Nat.zero_le (j i).val
    have hjhi : (j i : ℤ) < (3 ^ k : ℕ) := by exact_mod_cast (j i).isLt
    have hN' : ((3 ^ k : ℕ) : ℤ) = 2 * N + 1 := by dsimp only [N]; exact_mod_cast hN
    change -N ≤ v i ∧ v i ≤ N
    constructor <;> omega
  · intro hv
    have hN' : ((3 ^ k : ℕ) : ℤ) = 2 * N + 1 := by dsimp only [N]; exact_mod_cast hN
    let j : Fin d → Fin (3 ^ k) := fun i => ⟨(v i + N).toNat, by
      have hi := hv i
      have h0 : 0 ≤ v i + N := by change -N ≤ v i ∧ v i ≤ N at hi; omega
      have hhi : v i + N < (3 ^ k : ℕ) := by change -N ≤ v i ∧ v i ≤ N at hi; omega
      exact_mod_cast (show ((v i + N).toNat : ℤ) < ((3 ^ k : ℕ) : ℤ) by
        rw [Int.toNat_of_nonneg h0]; exact hhi)⟩
    refine ⟨(j, π), Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · funext i
      change (((v i + N).toNat : ℕ) : ℤ) - N = v i
      rw [Int.toNat_of_nonneg (by have hi := hv i; change -N ≤ v i ∧ v i ≤ N at hi; omega)]
      omega
    · rfl

/-- A grid cube center lying in the unit cube has an audited triangulation index. -/
lemma lower_grid_mem_of_center {d : ℕ} (k : ℕ) (v : Fin d → ℤ) (π : Equiv.Perm (Fin d))
    (hc : (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (v i : ℝ)) ∈ Aliases.originCube 1) :
    (v, π) ∈ triangulation k := by
  rw [lower_mem_triangulation_iff]
  have hh : 0 < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ (-(k : ℤ)) * ((3 ^ k : ℕ) : ℝ) = 1 := by
    simp only [zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  have hN := lower_grid_half_width k
  intro i
  have hi := hc i
  change -(1 / 2 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) * (v i : ℝ) ∧
      (3 : ℝ) ^ (-(k : ℤ)) * (v i : ℝ) < 1 / 2 at hi
  have hlo : -((3 ^ k : ℕ) : ℝ) < 2 * (v i : ℝ) := by nlinarith only [hi.1, hh, hscale]
  have hhi : 2 * (v i : ℝ) < ((3 ^ k : ℕ) : ℝ) := by nlinarith only [hi.2, hh, hscale]
  have hlo' : -((3 ^ k : ℕ) : ℤ) < 2 * v i := by exact_mod_cast hlo
  have hhi' : 2 * v i < ((3 ^ k : ℕ) : ℤ) := by exact_mod_cast hhi
  have hN' : ((3 ^ k : ℕ) : ℤ) = 2 * (((3 ^ k - 1) / 2 : ℕ) : ℤ) + 1 := by exact_mod_cast hN
  constructor <;> omega

lemma lower_child_grid_mem {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) (η : LowerChildIndex d) :
    lowerChildGrid c η ∈ triangulation k := by
  apply lower_grid_mem_of_center
  apply hQ
  have he : (fun i => (3 : ℝ) ^ (-(k : ℤ)) * ((lowerChildGrid c η).1 i : ℝ)) =
      lowerChildCenter k c η.1 := by
    funext i
    simp only [lowerChildGrid, lowerChildCenter, Int.cast_add, Int.cast_sub, Int.cast_natCast,
      Int.cast_one]
  change (fun i => (3 : ℝ) ^ (-(k : ℤ)) * ((lowerChildGrid c η).1 i : ℝ)) ∈ auxCube (k : ℤ) c
  rw [he]
  apply lower_child_cube_subset (k : ℤ) c η.1
  intro i
  simp only [sub_self]
  constructor <;> linarith only [zpow_pos (by norm_num : (0 : ℝ) < 3) (-(k : ℤ))]

def lowerChildEmbedding {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) : LowerChildIndex d ↪ SimplexIndex d k where
  toFun η := ⟨lowerChildGrid c η, lower_child_grid_mem k c hQ η⟩
  inj' := fun _ _ h => lower_child_grid_injective c (congrArg Subtype.val h)

lemma lower_child_embedding_cell {d : ℕ} (k : ℕ) (c : Fin d → ℤ)
    (hQ : auxCube (k : ℤ) c ⊆ Aliases.originCube 1) (η : LowerChildIndex d) :
    simplexCell k (lowerChildEmbedding k c hQ η) = lowerChildCell k c η := by
  change Aliases.simplex (-(k : ℤ)) η.2
    (fun i => (3 : ℝ) ^ (-(k : ℤ)) * ((lowerChildGrid c η).1 i : ℝ)) =
      Aliases.simplex (-(k : ℤ)) η.2 (lowerChildCenter k c η.1)
  congr 1
  funext i
  simp only [lowerChildGrid, lowerChildCenter, Int.cast_add, Int.cast_sub, Int.cast_natCast,
    Int.cast_one]

def lowerDescendantCenterIndex {d : ℕ} (m k : ℤ) (z n : Fin d → ℤ) : Fin d → ℤ :=
  fun i => z i * (3 : ℤ) ^ (k - m).toNat + 3 * n i

lemma lower_descendant_center {d : ℕ} (m k : ℤ) (hmk : m ≤ k) (z n : Fin d → ℤ) (i : Fin d) :
    (lowerDescendantCenterIndex m k z n i : ℝ) * (3 : ℝ) ^ (-k) =
      (z i : ℝ) * (3 : ℝ) ^ (-m) + (n i : ℝ) * (3 : ℝ) ^ (1 - k) := by
  unfold lowerDescendantCenterIndex
  push_cast
  rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hmk), add_mul,
    mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [show k - m + -k = -m by omega, lower_aux_side]
  ring

lemma lower_descendant_eq_auxCube {d : ℕ} (m k : ℤ) (hmk : m ≤ k) (z n : Fin d → ℤ) :
    auxDescendantCube m k z n = auxCube k (lowerDescendantCenterIndex m k z n) := by
  ext x
  change (∀ i, |x i - ((z i : ℝ) * (3 : ℝ) ^ (-m) +
    (n i : ℝ) * (3 : ℝ) ^ (1 - k))| < (3 : ℝ) ^ (1 - k) / 2) ↔ _
  simp only [auxCube, Set.mem_ofPred_eq, ← lower_descendant_center m k hmk z n]


end

end CoarseDeGiorgi.LowerFractional
