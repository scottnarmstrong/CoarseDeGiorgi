module

public import CoarseDeGiorgi.Endpoint.Rescaling.AffineMeasure
public import CoarseDeGiorgi.Moments.Cells

/-! The fixed interior lattice maps send every positive-level simplex to a global cell. -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped ENNReal Pointwise

namespace CoarseDeGiorgi.Endpoint.Rescaling

open Foundations.Simplex

noncomputable def latticeCenter {d : ℕ} (z : Fin d → ℤ) : Vec d := fun i => (z i : ℝ) / 81

theorem latticeCenter_scale {d : ℕ} (z : Fin d → ℤ) (l : ℕ) (η : SimplexIndex d (l + 1)) :
    (fun i => (3 : ℝ) ^ (-(l + 4 : ℕ) : ℤ) *
      ((3 ^ l : ℤ) * z i + η.1.1 i : ℤ)) =
    (1 / 27 : ℝ) • (fun i => (3 : ℝ) ^ (-(l + 1 : ℕ) : ℤ) * (η.1.1 i : ℝ)) +
      latticeCenter z := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, latticeCenter,
    Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, zpow_neg, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
    zpow_natCast, zpow_ofNat]
  field_simp
  ring

private theorem half_shift (l : ℕ) :
    ((3 ^ (l + 4) - 1) / 2 : ℕ) = 39 * 3 ^ l + (3 ^ (l + 1) - 1) / 2 := by
  have hodd : Odd (3 ^ (l + 1) : ℕ) := (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow
  obtain ⟨b, hb⟩ := hodd
  have he : 3 ^ (l + 4) = 81 * 3 ^ l := by rw [pow_add]; ring
  have he' : 3 ^ (l + 1) = 3 * 3 ^ l := by rw [pow_add]; ring
  omega

theorem latticeIndex_mem {d : ℕ} (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (l : ℕ) (η : SimplexIndex d (l + 1)) :
    (fun i => (3 ^ l : ℤ) * z i + η.1.1 i, η.1.2) ∈ triangulation (l + 4) := by
  classical
  obtain ⟨⟨j, π⟩, _, hj⟩ := Finset.mem_image.mp η.2
  have hej : (gridOffset (l + 1) j, π) = η.1 := hj
  let j' : Fin d → Fin (3 ^ (l + 4)) := fun i =>
    ⟨(3 ^ l * (z i + 39) + (j i).val).toNat, by
      have hz0 : 0 ≤ 3 ^ l * (z i + 39) + (j i).val := by
        have hp : (0 : ℤ) ≤ 3 ^ l := by positivity
        have hm := mul_nonneg hp (by linarith only [(hz i).1] : 0 ≤ z i + 39)
        omega
      have hm := mul_le_mul_of_nonneg_left (hz i).2 (by positivity : (0 : ℤ) ≤ 3 ^ l)
      have he : 3 ^ (l + 4) = 81 * 3 ^ l := by rw [pow_add]; ring
      have he' : 3 ^ (l + 1) = 3 * 3 ^ l := by rw [pow_add]; ring
      have hjlt := (j i).isLt
      zify at hjlt ⊢
      rw [Int.toNat_of_nonneg hz0]
      have heZ : (3 ^ (l + 4) : ℤ) = 81 * 3 ^ l := by exact_mod_cast he
      have heZ' : (3 ^ (l + 1) : ℤ) = 3 * 3 ^ l := by exact_mod_cast he'
      rw [heZ'] at hjlt
      rw [heZ]
      nlinarith only [hm, hjlt]⟩
  apply Finset.mem_image.mpr
  refine ⟨(j', π), Finset.mem_univ _, ?_⟩
  refine Prod.ext ?_ ?_
  · change gridOffset (l + 4) j' = _
    funext i
    have hz0 : 0 ≤ 3 ^ l * (z i + 39) + (j i).val := by
      have hm := mul_nonneg (by positivity : (0 : ℤ) ≤ 3 ^ l)
        (by linarith only [(hz i).1] : 0 ≤ z i + 39)
      omega
    have hηi := congrFun (congrArg Prod.fst hej) i
    simp only [gridOffset] at hηi
    simp only [gridOffset, j', Int.toNat_of_nonneg hz0, half_shift, Nat.cast_add,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← hηi]
    ring
  · change π = η.1.2
    exact congrArg Prod.snd hej

/-- The injection from level `l+1` to level `l+4` at a fixed lattice center. -/
def latticeIndex {d : ℕ} (z : Fin d → ℤ) (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39)
    (l : ℕ) (η : SimplexIndex d (l + 1)) : SimplexIndex d (l + 4) :=
  ⟨(fun i => (3 ^ l : ℤ) * z i + η.1.1 i, η.1.2), latticeIndex_mem z hz l η⟩

theorem latticeIndex_injective {d : ℕ} (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (l : ℕ) :
    Function.Injective (latticeIndex z hz l) := by
  intro η τ h
  have hv := congrArg Subtype.val h
  change (fun i => (3 ^ l : ℤ) * z i + η.1.1 i, η.1.2) =
    (fun i => (3 ^ l : ℤ) * z i + τ.1.1 i, τ.1.2) at hv
  have hs := congrArg
    (fun θ : (Fin d → ℤ) × Equiv.Perm (Fin d) => θ.2) hv
  have hz' : η.1.1 = τ.1.1 := by
    funext i
    have hfst := congrArg (fun θ : (Fin d → ℤ) × Equiv.Perm (Fin d) => θ.1) hv
    exact add_left_cancel (congrFun hfst i)
  exact Subtype.ext (Prod.ext hz' hs)

theorem affineImage_simplex {d : ℕ} (y c : Vec d) (n : ℤ)
    (π : Equiv.Perm (Fin d)) :
    affineImage y (1 / 27) (CoarseDeGiorgi.simplex n π c) =
      CoarseDeGiorgi.simplex (n - 3) π ((1 / 27 : ℝ) • c + y) := by
  have hs : (3 : ℝ) ^ (n - 3) = (1 / 27) * (3 : ℝ) ^ n := by
    rw [zpow_sub₀ (by norm_num)]
    norm_num
    ring
  rw [← affineMap_image]
  ext x
  constructor
  · rintro ⟨v, ⟨w, rfl, hb, ho⟩, rfl⟩
    refine ⟨w, ?_, hb, ho⟩
    funext i
    simp only [affineMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    ring
  · rintro ⟨w, rfl, hb, ho⟩
    refine ⟨c + (3 : ℝ) ^ n • w, ⟨w, rfl, hb, ho⟩, ?_⟩
    funext i
    simp only [affineMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    ring

/-- Exact cell-image identity underlying the shifted moment comparison. -/
theorem affineImage_simplexCell {d : ℕ} (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (l : ℕ) (η : SimplexIndex d (l + 1)) :
    affineImage (latticeCenter z) (1 / 27) (simplexCell (l + 1) η) =
      simplexCell (l + 4) (latticeIndex z hz l η) := by
  unfold simplexCell
  rw [affineImage_simplex, ← latticeCenter_scale]
  have he : -(↑(l + 1) : ℤ) - 3 = -(↑(l + 4) : ℤ) := by omega
  rw [he]
  rfl

end CoarseDeGiorgi.Endpoint.Rescaling
