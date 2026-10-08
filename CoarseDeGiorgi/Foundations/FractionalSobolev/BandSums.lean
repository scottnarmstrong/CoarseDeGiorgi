import CoarseDeGiorgi.Foundations.FractionalSobolev.Sequence

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open MeasureTheory
open scoped ENNReal
noncomputable section

lemma sequenceWeight_prefix {T : ℝ} (hT : 1 < T) (l : ℤ) :
    (∑' i : ℤ, if i ≤ l then sequenceWeight T i else 0) =
      sequenceWeight T l * ENNReal.ofReal (T / (T - 1)) := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  rw [← (Equiv.addRight l).tsum_eq (fun i : ℤ => if i ≤ l then sequenceWeight T i else 0)]
  change (∑' i : ℤ, if i + l ≤ l then sequenceWeight T (i + l) else 0) = _
  rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hnonneg : (∑' i : ℕ, if (i : ℤ) + l ≤ l then sequenceWeight T ((i : ℤ) + l) else 0) =
      sequenceWeight T l := by
    rw [ENNReal.tsum_eq_add_tsum_ite 0]
    simp only [Nat.cast_zero, zero_add, le_refl, ite_true]
    suffices (∑' b : ℕ, if b = 0 then 0 else
        if (b : ℤ) + l ≤ l then sequenceWeight T ((b : ℤ) + l) else 0) = 0 by exact (congrArg (fun z => sequenceWeight T l + z) this).trans (add_zero _)
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    split_ifs with hb hc
    · rfl
    · omega
    · rfl
  rw [hnonneg]
  have hneg : (∑' i : ℕ, if -((i : ℤ) + 1) + l ≤ l then
      sequenceWeight T (-((i : ℤ) + 1) + l) else 0) =
      sequenceWeight T l * (ENNReal.ofReal T)⁻¹ * (1 - (ENNReal.ofReal T)⁻¹)⁻¹ := by
    have heq : ∀ i : ℕ, (if -((i : ℤ) + 1) + l ≤ l then
        sequenceWeight T (-((i : ℤ) + 1) + l) else 0) =
        sequenceWeight T l * (ENNReal.ofReal T)⁻¹ ^ (i + 1) := by
      intro i
      rw [ite_eq_left (by omega), sequenceWeight_add hT0, mul_comm]
      congr 1
      simpa only [Nat.cast_add, Nat.cast_one] using sequenceWeight_neg_nat hT0 (i + 1)
    simp_rw [heq]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, mul_assoc]
  have hgeo : (∑' i : ℕ, (ENNReal.ofReal T)⁻¹ ^ i) = ENNReal.ofReal (T / (T - 1)) := by
    rw [ENNReal.tsum_geometric, ← ENNReal.ofReal_inv_of_pos hT0,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (inv_nonneg.mpr hT0.le),
      ← ENNReal.ofReal_inv_of_pos (by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hT)]
    congr 1
    field_simp
  calc
    _ = sequenceWeight T l * (1 + ∑' i : ℕ, (ENNReal.ofReal T)⁻¹ ^ (i + 1)) := by
      rw [ENNReal.tsum_geometric_add_one, mul_add, mul_one, hneg, mul_assoc]
    _ = sequenceWeight T l * ∑' i : ℕ, (ENNReal.ofReal T)⁻¹ ^ i := by
      congr 1
      simpa only [pow_zero] using (tsum_eq_zero_add' (f := fun i : ℕ => (ENNReal.ofReal T)⁻¹ ^ i) ENNReal.summable).symm
    _ = _ := congrArg (sequenceWeight T l * ·) hgeo

/-- Tonelli's discrete convolution estimate, with finite sums above the cutoff. -/
lemma band_sum_bound {T θ : ℝ} (hT : 1 < T) (hθ : 0 < θ)
    {a d : ℤ → ℝ≥0∞} (ha : Antitone a) {N : ℤ}
    (hd : ∀ l, N ≤ l → d l = 0)
    (hdecomp : ∀ i, a i = ∑ l ∈ Finset.Ico i N, d l) :
    (∑' i, sequenceWeight T i * (a (i - 1)) ^ (-θ) * a i) ≤
      ENNReal.ofReal (T / (T - 1)) *
        ∑' l, sequenceWeight T l * (a (l - 1)) ^ (-θ) * d l := by
  classical
  have heq : ∀ i, sequenceWeight T i * (a (i - 1)) ^ (-θ) * a i =
      ∑' l : ℤ, if i ≤ l then sequenceWeight T i * (a (i - 1)) ^ (-θ) * d l else 0 := by
    intro i
    rw [hdecomp i, Finset.mul_sum]
    symm
    calc
      _ = ∑ l ∈ Finset.Ico i N, if i ≤ l then
          sequenceWeight T i * (a (i - 1)) ^ (-θ) * d l else 0 := by
        apply tsum_eq_sum
        intro l hl
        by_cases hil : i ≤ l
        · rw [ite_eq_left hil, hd l (by simpa [Finset.mem_Ico, hil] using hl), mul_zero]
        · rw [ite_eq_right hil]
      _ = _ := Finset.sum_congr rfl (fun l hl => ite_eq_left (Finset.mem_Ico.mp hl).1)
  simp_rw [heq]
  rw [ENNReal.tsum_comm]
  calc
    _ ≤ ∑' l : ℤ, ∑' i : ℤ, if i ≤ l then sequenceWeight T i *
        (a (l - 1)) ^ (-θ) * d l else 0 := by
      apply ENNReal.tsum_le_tsum
      intro l
      apply ENNReal.tsum_le_tsum
      intro i
      split_ifs with hil
      · rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact mul_le_mul' (mul_le_mul' le_rfl
          (ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ha (by omega)) hθ.le))) le_rfl
      · exact le_rfl
    _ = ENNReal.ofReal (T / (T - 1)) *
        ∑' l, sequenceWeight T l * (a (l - 1)) ^ (-θ) * d l := by
      have hterm : ∀ l : ℤ, (∑' i : ℤ, if i ≤ l then sequenceWeight T i *
          (a (l - 1)) ^ (-θ) * d l else 0) =
          ENNReal.ofReal (T / (T - 1)) * (sequenceWeight T l * (a (l - 1)) ^ (-θ) * d l) := by
        intro l
        have hfun : (fun i : ℤ => if i ≤ l then sequenceWeight T i *
            (a (l - 1)) ^ (-θ) * d l else 0) =
            fun i : ℤ => (if i ≤ l then sequenceWeight T i else 0) *
              (a (l - 1)) ^ (-θ) * d l := by
          funext i
          split_ifs <;> simp
        rw [hfun, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, sequenceWeight_prefix hT]
        ac_rfl
      simp_rw [hterm]
      exact ENNReal.tsum_mul_left

lemma band_sum_bound_shift {T θ : ℝ} (hT : 1 < T) (hθ : 0 < θ)
    {a d : ℤ → ℝ≥0∞} (ha : Antitone a) {N : ℤ}
    (hd : ∀ l, N ≤ l → d l = 0)
    (hdecomp : ∀ i, a i = ∑ l ∈ Finset.Ico i N, d l) :
    (∑' i, sequenceWeight T (i - 1) * (a (i - 1)) ^ (-θ) * a i) ≤
      ENNReal.ofReal (T / (T - 1)) *
        ∑' l, sequenceWeight T (l - 1) * (a (l - 1)) ^ (-θ) * d l := by
  have hshift : ∀ i : ℤ, sequenceWeight T (i - 1) = sequenceWeight T (-1) * sequenceWeight T i := by
    intro i
    rw [sub_eq_add_neg, sequenceWeight_add (lt_trans zero_lt_one hT), mul_comm]
  simp_rw [hshift, mul_assoc, ENNReal.tsum_mul_left]
  simpa only [mul_assoc, mul_comm (ENNReal.ofReal (T / (T - 1)))] using
    (mul_le_mul' (le_rfl : sequenceWeight T (-1) ≤ sequenceWeight T (-1))
      (band_sum_bound hT hθ ha hd hdecomp))

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
