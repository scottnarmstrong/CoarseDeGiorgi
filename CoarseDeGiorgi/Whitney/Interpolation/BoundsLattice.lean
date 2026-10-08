import CoarseDeGiorgi.Whitney.Interpolation.BoundsBary

/-!
# Lattice points of a Kuhn simplex are vertices

`lat t a` says that `a` is a coordinate of the vertex lattice `t (ℤ - 1/2)` of mesh `t`.
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset

variable {d : ℕ}

/-- `a` is a coordinate of a vertex of the mesh of size `t`. -/
def lat (t a : ℝ) : Prop := ∃ k : ℤ, a = t * ((k : ℝ) - 1 / 2)

theorem lat_mono {a b : ℤ} (hab : b ≤ a) {w : ℝ} (hw : lat ((3 : ℝ) ^ a) w) :
    lat ((3 : ℝ) ^ b) w := by
  obtain ⟨k, rfl⟩ := hw
  obtain ⟨m, rfl⟩ := Int.exists_add_of_le hab
  refine ⟨3 ^ m * k - (3 ^ m - 1) / 2, ?_⟩
  have h3 : (3 : ℤ) ^ m % 2 = 1 := by
    exact Int.odd_iff.mp (Odd.pow (by decide))
  have hdiv : (2 : ℤ) * ((3 ^ m - 1) / 2) = 3 ^ m - 1 := by omega
  have hdivR : (2 : ℝ) * (((3 ^ m - 1) / 2 : ℤ) : ℝ) = 3 ^ m - 1 := by exact_mod_cast hdiv
  have hz : (3 : ℝ) ^ (b + (m : ℤ)) = 3 ^ b * 3 ^ m := by
    rw [zpow_add₀ (by norm_num)]; simp
  rw [hz]
  push_cast
  have hq : (3 : ℝ) ^ m = 2 * (((3 ^ m - 1) / 2 : ℤ) : ℝ) + 1 := by linarith
  rw [hq]
  ring

theorem box_coord {t zi A B xi c : ℝ} (ht : 0 < t) (hz : ∃ k : ℤ, zi = t * k) (hA : lat t A)
    (hB : lat t B) (hAx : A ≤ xi) (hxB : xi ≤ B) (hx1 : zi - t / 2 ≤ xi ∧ xi ≤ zi + t / 2)
    (hc : c = -(1 / 2) ∨ c = 1 / 2) (hlt : c = -(1 / 2) → xi < zi + t / 2)
    (hgt : c = 1 / 2 → zi - t / 2 < xi) : A ≤ zi + t * c ∧ zi + t * c ≤ B := by
  obtain ⟨kz, hkz⟩ := hz
  obtain ⟨kA, hkA⟩ := hA
  obtain ⟨kB, hkB⟩ := hB
  rcases hc with rfl | rfl
  · have h1 := hlt rfl
    have : (kA : ℝ) < kz + 1 := by
      have : t * ((kA : ℝ) - 1 / 2) < t * ((kz : ℝ) + 1 / 2) := by
        rw [← hkA]; nlinarith
      have := lt_of_mul_lt_mul_left this ht.le
      linarith
    have hk : kA ≤ kz := by
      have : kA < kz + 1 := by exact_mod_cast this
      omega
    have hkR : (kA : ℝ) ≤ kz := by exact_mod_cast hk
    constructor
    · rw [hkA, hkz]; nlinarith
    · linarith [hx1.1]
  · have h1 := hgt rfl
    have : (kz : ℝ) < kB := by
      have : t * ((kz : ℝ) - 1 / 2) < t * ((kB : ℝ) - 1 / 2) := by
        rw [← hkB]; nlinarith
      have := lt_of_mul_lt_mul_left this ht.le
      linarith
    have hk : kz + 1 ≤ kB := by
      have : kz < kB := by exact_mod_cast this
      omega
    have hkR : (kz : ℝ) + 1 ≤ kB := by exact_mod_cast hk
    constructor
    · linarith [hx1.2]
    · rw [hkB, hkz]; nlinarith

theorem exists_kv_of_lat {t : ℝ} (ht : 0 < t) {π : Equiv.Perm (Fin d)} {z x : Vec d}
    (hx : x ∈ closedKuhn t π z) (hz : ∀ i, ∃ k : ℤ, z i = t * k) (hl : ∀ i, lat t (x i)) :
    ∃ j : Fin (d + 1), x = kv t π z j := by
  have hf : ∀ i, (x i - z i) / t + 1 / 2 = 0 ∨ (x i - z i) / t + 1 / 2 = 1 := by
    intro i
    obtain ⟨k, hk⟩ := hl i
    obtain ⟨kz, hkz⟩ := hz i
    have e : (x i - z i) / t + 1 / 2 = ((k - kz : ℤ) : ℝ) := by
      rw [hk, hkz]; push_cast; field_simp; ring
    have h0 := frac_nonneg ht hx i
    have h1 := frac_le_one ht hx i
    rw [e] at h0 h1 ⊢
    have a0 : (0 : ℤ) ≤ k - kz := by exact_mod_cast h0
    have a1 : k - kz ≤ 1 := by exact_mod_cast h1
    rcases (by omega : k - kz = 0 ∨ k - kz = 1) with h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
  have hb : ∀ k, bs t π z x k = 0 ∨ bs t π z x k = 1 := by
    intro k
    unfold bs
    split_ifs
    · left; rfl
    · exact hf _
    · right; rfl
  have hex : ∃ k, bs t π z x (k + 1) = 1 := ⟨d, bs_top⟩
  classical
  let j := Nat.find hex
  have hjd : j ≤ d := Nat.find_min' hex bs_top
  refine ⟨⟨j, by omega⟩, ?_⟩
  funext i
  have hi : (π.symm i).val < d := (π.symm i).isLt
  have hxi : x i = z i + t * (bs t π z x ((π.symm i).val + 1) - 1 / 2) := by
    rw [bs_idx]; field_simp; ring
  rw [hxi]
  simp only [kv]
  by_cases hij : (π.symm i).val < j
  · have hn := Nat.find_min hex hij
    have : bs t π z x ((π.symm i).val + 1) = 0 := (hb _).resolve_right hn
    rw [ite_eq_left hij, this]; ring
  · have hspec : bs t π z x (j + 1) = 1 := Nat.find_spec hex
    have h1 := bs_mono ht hx (show j + 1 ≤ (π.symm i).val + 1 by omega) (by omega)
    have h2 := bs_le_one ht hx ((π.symm i).val + 1)
    have : bs t π z x ((π.symm i).val + 1) = 1 := by linarith
    rw [ite_eq_right hij, this]; ring

end CoarseDeGiorgi.WhitneyInterp
