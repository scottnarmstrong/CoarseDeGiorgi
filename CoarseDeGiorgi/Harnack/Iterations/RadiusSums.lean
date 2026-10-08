import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Finite partial sums of the geometric radius weights are bounded by the source
constant `χ / (χ - 1)`.
-/
theorem radius_geometric_sum_le {χ : ℝ} (hχ : 1 < χ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (χ⁻¹) ^ j) ≤ χ / (χ - 1) := by
  let q : ℝ := χ⁻¹
  have hχ0 : 0 < χ := lt_trans zero_lt_one hχ
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (inv_lt_one₀ hχ0).2 hχ
  have hden : 0 < 1 - q := by linarith
  have hgeom (m : ℕ) :
      (1 - q) * (∑ j ∈ Finset.range m, q ^ j) = 1 - q ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [pow_succ]
      calc
        (1 - q) * ((∑ j ∈ Finset.range m, q ^ j) + q ^ m) =
            (1 - q) * (∑ j ∈ Finset.range m, q ^ j) + (1 - q) * q ^ m := by ring
        _ = (1 - q ^ m) + (1 - q) * q ^ m := by rw [ih]
        _ = 1 - q ^ m * q := by ring
  have hqpow : 0 ≤ q ^ n := pow_nonneg hq0.le _
  have hsum :
      (∑ j ∈ Finset.range n, q ^ j) ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ hden).2
    rw [mul_comm]
    rw [hgeom]
    nlinarith
  have hratio : 1 / (1 - q) = χ / (χ - 1) := by
    dsimp [q]
    field_simp
  simpa [q, hratio] using hsum

/-- Finite partial sums with the linear iteration cost are bounded by the squared
geometric-series constant.
-/
theorem radius_weighted_geometric_sum_le {χ : ℝ} (hχ : 1 < χ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (χ⁻¹) ^ j) ≤
      χ ^ 2 / (χ - 1) ^ 2 := by
  let q : ℝ := χ⁻¹
  have hχ0 : 0 < χ := lt_trans zero_lt_one hχ
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (inv_lt_one₀ hχ0).2 hχ
  have hqle : q ≤ 1 := le_of_lt hq1
  have hden : 0 < 1 - q := by linarith
  have hden2 : 0 < (1 - q) ^ 2 := sq_pos_of_pos hden
  have hweighted (m : ℕ) :
      (1 - q) ^ 2 *
          (∑ j ∈ Finset.range m, ((j : ℝ) + 1) * q ^ j) =
        1 - ((m : ℝ) + 1) * q ^ m + (m : ℝ) * q ^ (m + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        (1 - q) ^ 2 *
            (∑ j ∈ Finset.range (m + 1), ((j : ℝ) + 1) * q ^ j) =
          (1 - q) ^ 2 *
          ((∑ j ∈ Finset.range m, ((j : ℝ) + 1) * q ^ j) +
              ((m : ℝ) + 1) * q ^ m) := by
                rw [Finset.sum_range_succ]
        _ = (1 - ((m : ℝ) + 1) * q ^ m + (m : ℝ) * q ^ (m + 1)) +
              (1 - q) ^ 2 * (((m : ℝ) + 1) * q ^ m) := by
                rw [mul_add, ih]
        _ = 1 - (((m + 1 : ℕ) : ℝ) + 1) * q ^ (m + 1) +
              ((m + 1 : ℕ) : ℝ) * q ^ ((m + 1) + 1) := by
                have hm : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
                rw [hm]
                ring
  have hpow : 0 ≤ q ^ n := pow_nonneg hq0.le _
  have hlinear : (n : ℝ) * q ≤ n := by
    exact mul_le_of_le_one_right (by positivity) hqle
  have htail : -(((n : ℝ) + 1) * q ^ n) +
      (n : ℝ) * q ^ (n + 1) ≤ 0 := by
    rw [pow_succ]
    nlinarith [mul_nonneg hpow (show 0 ≤ (n : ℝ) * (1 - q) + 1 by nlinarith)]
  have hsum :
      (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * q ^ j) ≤ 1 / (1 - q) ^ 2 := by
    apply (le_div_iff₀ hden2).2
    rw [mul_comm, hweighted]
    nlinarith
  have hratio : 1 / (1 - q) ^ 2 = χ ^ 2 / (χ - 1) ^ 2 := by
    dsimp [q]
    field_simp
  simpa [q, hratio] using hsum

/-- The logarithmic cost of a finite chain with an affine-in-index cost is
controlled uniformly by the two geometric sums.
-/
theorem radius_affine_cost_sum_le {χ A B : ℝ} (hχ : 1 < χ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (n : ℕ) :
    (∑ j ∈ Finset.range n,
        (χ⁻¹) ^ j * (A + B * ((j : ℝ) + 1))) ≤
      A * (χ / (χ - 1)) + B * (χ ^ 2 / (χ - 1) ^ 2) := by
  have hsum := radius_geometric_sum_le hχ n
  have hweighted := radius_weighted_geometric_sum_le hχ n
  have hrewrite :
        (∑ j ∈ Finset.range n,
          (χ⁻¹) ^ j * (A + B * ((j : ℝ) + 1))) =
        A * (∑ j ∈ Finset.range n, (χ⁻¹) ^ j) +
          B * (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (χ⁻¹) ^ j) := by
    calc
      _ = ∑ j ∈ Finset.range n,
          (A * (χ⁻¹) ^ j + B * (((j : ℝ) + 1) * (χ⁻¹) ^ j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ j ∈ Finset.range n, A * (χ⁻¹) ^ j) +
          (∑ j ∈ Finset.range n, B * (((j : ℝ) + 1) * (χ⁻¹) ^ j)) :=
            Finset.sum_add_distrib
      _ = A * (∑ j ∈ Finset.range n, (χ⁻¹) ^ j) +
          B * (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (χ⁻¹) ^ j) := by
            rw [Finset.mul_sum, Finset.mul_sum]
  rw [hrewrite]
  exact add_le_add (mul_le_mul_of_nonneg_left hsum hA)
    (mul_le_mul_of_nonneg_left hweighted hB)

end CoarseDeGiorgi.Harnack.Iterations
