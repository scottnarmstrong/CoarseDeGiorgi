import CoarseDeGiorgi.Whitney.Interpolation.BoundsBasic

/-!
# Barycentric coordinates on a closed Kuhn simplex
-/

namespace CoarseDeGiorgi.WhitneyInterp

open Homogenization Set Finset

variable {d : ℕ}

/-- The sorted normalized coordinates, padded by `0` in front and `1` at the end. -/
noncomputable def bs (t : ℝ) (π : Equiv.Perm (Fin d)) (z x : Vec d) (k : ℕ) : ℝ :=
  if k = 0 then 0 else if h : k - 1 < d then
    (x (π ⟨k - 1, h⟩) - z (π ⟨k - 1, h⟩)) / t + 1 / 2 else 1

section bs

variable {t : ℝ} {π : Equiv.Perm (Fin d)} {z x : Vec d}

theorem bs_zero : bs t π z x 0 = 0 := by simp [bs]

theorem bs_top : bs t π z x (d + 1) = 1 := by simp [bs]

theorem bs_idx (i : Fin d) :
    bs t π z x ((π.symm i).val + 1) = (x i - z i) / t + 1 / 2 := by
  simp [bs]

theorem frac_nonneg (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (i : Fin d) :
    0 ≤ (x i - z i) / t + 1 / 2 := by
  have h := (hx.1 i).1
  have : -(1 / 2 : ℝ) ≤ (x i - z i) / t := by
    rw [le_div_iff₀ ht]; linarith
  linarith

theorem frac_le_one (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (i : Fin d) :
    (x i - z i) / t + 1 / 2 ≤ 1 := by
  have h := (hx.1 i).2
  have : (x i - z i) / t ≤ 1 / 2 := by
    rw [div_le_iff₀ ht]; linarith
  linarith

theorem bs_nonneg (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (k : ℕ) : 0 ≤ bs t π z x k := by
  unfold bs
  split_ifs
  · exact le_refl _
  · exact frac_nonneg ht hx _
  · exact zero_le_one

theorem bs_le_one (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (k : ℕ) : bs t π z x k ≤ 1 := by
  unfold bs
  split_ifs
  · exact zero_le_one
  · exact frac_le_one ht hx _
  · exact le_refl _

theorem bs_succ_le (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (k : ℕ) (hk : k ≤ d) :
    bs t π z x k ≤ bs t π z x (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [bs_zero]; exact bs_nonneg ht hx _
  · have hk1 : k - 1 < d := by omega
    have e1 : bs t π z x k = (x (π ⟨k - 1, hk1⟩) - z (π ⟨k - 1, hk1⟩)) / t + 1 / 2 := by
      unfold bs
      rw [ite_eq_right (by omega), dite_eq_left hk1]
    rw [e1]
    by_cases hkd : k < d
    · have e2 : bs t π z x (k + 1) = (x (π ⟨k, hkd⟩) - z (π ⟨k, hkd⟩)) / t + 1 / 2 := by
        unfold bs
        rw [ite_eq_right (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [dite_eq_left hkd]
      rw [e2]
      have := hx.2 ⟨k - 1, hk1⟩ ⟨k, hkd⟩ (by
        show k - 1 < k
        omega)
      have := div_le_div_of_nonneg_right this ht.le
      linarith
    · have e2 : bs t π z x (k + 1) = 1 := by
        unfold bs
        rw [ite_eq_right (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [dite_eq_right hkd]
      rw [e2]
      exact frac_le_one ht hx _

theorem bs_mono (ht : 0 < t) (hx : x ∈ closedKuhn t π z) {j k : ℕ} (hjk : j ≤ k)
    (hk : k ≤ d + 1) : bs t π z x j ≤ bs t π z x k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_refl _
  | succ k hjk ih =>
    exact (ih (by omega)).trans (bs_succ_le ht hx k (by omega))

/-- The barycentric weight of vertex `j`. -/
noncomputable def lam (t : ℝ) (π : Equiv.Perm (Fin d)) (z x : Vec d) (j : Fin (d + 1)) : ℝ :=
  bs t π z x (j.val + 1) - bs t π z x j.val

theorem lam_nonneg (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (j : Fin (d + 1)) :
    0 ≤ lam t π z x j := by
  have := bs_succ_le ht hx j.val (by omega)
  unfold lam; linarith

theorem sum_lam : ∑ j, lam t π z x j = 1 := by
  unfold lam
  rw [Fin.sum_univ_eq_sum_range (fun j => bs t π z x (j + 1) - bs t π z x j) (d + 1),
    Finset.sum_range_sub (fun j => bs t π z x j) (d + 1), bs_top, bs_zero]
  norm_num

theorem sum_lam_tail (i : Fin d) :
    ∑ j : Fin (d + 1), (if (π.symm i).val < j.val then lam t π z x j else 0) =
      1 - bs t π z x ((π.symm i).val + 1) := by
  have hi : (π.symm i).val < d := (π.symm i).isLt
  unfold lam
  rw [Fin.sum_univ_eq_sum_range (fun j => if (π.symm i).val < j then
    bs t π z x (j + 1) - bs t π z x j else 0) (d + 1)]
  rw [← Finset.sum_filter]
  have hfil : (Finset.range (d + 1)).filter (fun j => (π.symm i).val < j) =
      Finset.Ico ((π.symm i).val + 1) (d + 1) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfil, Finset.sum_Ico_eq_sub _ (by omega : (π.symm i).val + 1 ≤ d + 1),
    Finset.sum_range_sub (fun j => bs t π z x j), Finset.sum_range_sub (fun j => bs t π z x j),
    bs_top, bs_zero]
  ring

theorem eq_sum_lam_kv (ht : 0 < t) (i : Fin d) :
    x i = ∑ j, lam t π z x j * kv t π z j i := by
  have hc : ∀ j : Fin (d + 1), lam t π z x j * kv t π z j i =
      lam t π z x j * z i + t * (1 / 2 * lam t π z x j) -
        t * (if (π.symm i).val < j.val then lam t π z x j else 0) := by
    intro j
    simp only [kv]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun j _ => hc j), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, sum_lam]
  simp only [← Finset.mul_sum]
  rw [sum_lam_tail, bs_idx]
  field_simp
  ring

theorem lam_support_lt (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (j : Fin (d + 1)) (i : Fin d)
    (hj : lam t π z x j ≠ 0) (hij : (π.symm i).val < j.val) : x i < z i + t / 2 := by
  by_contra hcon
  push Not at hcon
  have hf1 : bs t π z x ((π.symm i).val + 1) = 1 := by
    rw [bs_idx]
    have h1 := frac_le_one ht hx i
    have h2 : 1 ≤ (x i - z i) / t + 1 / 2 := by
      have : 1 / 2 ≤ (x i - z i) / t := by
        rw [le_div_iff₀ ht]; linarith
      linarith
    linarith
  have h1 : bs t π z x ((π.symm i).val + 1) ≤ bs t π z x j.val :=
    bs_mono ht hx (by omega) (by omega)
  have h2 := bs_le_one ht hx (j.val + 1)
  have h3 := lam_nonneg ht hx j
  unfold lam at h3 hj
  apply hj
  linarith

theorem lam_support_gt (ht : 0 < t) (hx : x ∈ closedKuhn t π z) (j : Fin (d + 1)) (i : Fin d)
    (hj : lam t π z x j ≠ 0) (hij : ¬ (π.symm i).val < j.val) : z i - t / 2 < x i := by
  by_contra hcon
  push Not at hcon
  have hf0 : bs t π z x ((π.symm i).val + 1) ≤ 0 := by
    rw [bs_idx]
    have : (x i - z i) / t ≤ -(1 / 2) := by
      rw [div_le_iff₀ ht]; linarith
    linarith
  have h1 : bs t π z x (j.val + 1) ≤ bs t π z x ((π.symm i).val + 1) :=
    bs_mono ht hx (by omega) (by omega)
  have h2 := bs_nonneg ht hx j.val
  have h3 := lam_nonneg ht hx j
  unfold lam at h3 hj
  apply hj
  linarith

/-- Barycentric representation of the points of a closed Kuhn simplex. -/
theorem bary (ht : 0 < t) (hx : x ∈ closedKuhn t π z) :
    ∃ l : Fin (d + 1) → ℝ, (∀ j, 0 ≤ l j) ∧ ∑ j, l j = 1 ∧
      (∀ i, x i = ∑ j, l j * kv t π z j i) ∧
      ∀ j i, l j ≠ 0 →
        ((π.symm i).val < j.val → x i < z i + t / 2) ∧
          (¬ (π.symm i).val < j.val → z i - t / 2 < x i) :=
  ⟨lam t π z x, lam_nonneg ht hx, sum_lam, fun i => eq_sum_lam_kv ht i, fun j i hj =>
    ⟨lam_support_lt ht hx j i hj, lam_support_gt ht hx j i hj⟩⟩

end bs

end CoarseDeGiorgi.WhitneyInterp
