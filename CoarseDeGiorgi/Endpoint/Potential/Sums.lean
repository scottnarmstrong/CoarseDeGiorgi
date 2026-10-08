import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace CoarseDeGiorgi.Endpoint.Potential

open Finset
open scoped ENNReal

/-- The scale sums `c_N` of the endpoint argument, with geometric weights `ρ₁`, `ρ₂`. -/
noncomputable def scaleSum (ρ₁ ρ₂ : ℝ≥0∞) (b : ℕ → ℝ≥0∞) (N : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Icc 1 N, ρ₁ ^ (N - k) * b k + ∑' k, (if N < k then ρ₂ ^ (k - N) * b k else 0)

theorem tsum_geom_shift (ρ : ℝ≥0∞) (k : ℕ) :
    ∑' N, (if k ≤ N then ρ ^ (N - k) else 0) ≤ (1 - ρ)⁻¹ := by
  rw [← ENNReal.tsum_geometric]
  rw [← Summable.sum_add_tsum_nat_add' (f := fun N => if k ≤ N then ρ ^ (N - k) else 0) (k := k)
    ENNReal.summable]
  have h0 : ∑ i ∈ range k, (if k ≤ i then ρ ^ (i - k) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [not_le.2 (Finset.mem_range.1 hi)]
  rw [h0, zero_add]
  apply le_of_eq
  congr 1
  funext j
  simp

theorem sum_geom_reflect_le (ρ : ℝ≥0∞) (hρ : ρ ≤ 1) (k : ℕ) :
    ∑ N ∈ range k, ρ ^ (k - N) ≤ (1 - ρ)⁻¹ := by
  rw [← ENNReal.tsum_geometric]
  calc ∑ N ∈ range k, ρ ^ (k - N) ≤ ∑ N ∈ range k, ρ ^ (k - 1 - N) := by
        apply Finset.sum_le_sum
        intro N hN
        have hN' := Finset.mem_range.1 hN
        have : k - N = (k - 1 - N) + 1 := by omega
        rw [this, pow_succ]
        exact mul_le_of_le_one_right zero_le hρ
    _ = ∑ N ∈ range k, ρ ^ N := Finset.sum_range_reflect (fun j => ρ ^ j) k
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- The sum over scales of `c_N` is bounded by a geometric constant times `∑ b_k`. -/
theorem tsum_scaleSum_le (ρ₁ ρ₂ : ℝ≥0∞) (h₂ : ρ₂ ≤ 1) (b : ℕ → ℝ≥0∞) :
    ∑' N, scaleSum ρ₁ ρ₂ b N ≤ ((1 - ρ₁)⁻¹ + (1 - ρ₂)⁻¹) * ∑' k, b k := by
  unfold scaleSum
  rw [ENNReal.tsum_add, add_mul]
  apply add_le_add
  · -- first sum
    have e1 : ∀ N, ∑ k ∈ Icc 1 N, ρ₁ ^ (N - k) * b k =
        ∑' k, (if k ∈ Icc 1 N then ρ₁ ^ (N - k) * b k else 0) := by
      intro N
      rw [tsum_eq_sum (s := Icc 1 N)]
      · exact Finset.sum_congr rfl fun k hk => by simp [hk]
      · intro k hk; simp [hk]
    simp_rw [e1]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    calc ∑' N, (if k ∈ Icc 1 N then ρ₁ ^ (N - k) * b k else 0)
        ≤ ∑' N, (if k ≤ N then ρ₁ ^ (N - k) else 0) * b k := by
          apply ENNReal.tsum_le_tsum
          intro N
          by_cases h : k ∈ Icc 1 N
          · simp [h, (Finset.mem_Icc.1 h).2]
          · simp [h]
      _ = (∑' N, (if k ≤ N then ρ₁ ^ (N - k) else 0)) * b k := ENNReal.tsum_mul_right
      _ ≤ _ := by gcongr; exact tsum_geom_shift ρ₁ k
  · -- second sum
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    have e : ∑' N, (if N < k then ρ₂ ^ (k - N) * b k else 0) =
        ∑ N ∈ range k, ρ₂ ^ (k - N) * b k := by
      rw [tsum_eq_sum (s := range k)]
      · exact Finset.sum_congr rfl fun N hN => by simp [Finset.mem_range.1 hN]
      · intro N hN; simp [Finset.mem_range] at hN; simp [not_lt.2 hN]
    rw [e, ← Finset.sum_mul]
    gcongr
    exact sum_geom_reflect_le ρ₂ h₂ k

/-- `ℓ^p ≤ ℓ^1` for `p ≥ 1`. -/
theorem tsum_rpow_le_rpow_tsum (c : ℕ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    ∑' N, c N ^ p ≤ (∑' N, c N) ^ p := by
  set S := ∑' N, c N with hS
  by_cases hSt : S = ⊤
  · rw [hSt, ENNReal.top_rpow_of_pos (by linarith)]; exact le_top
  have hle : ∀ N, c N ≤ S := fun N => ENNReal.le_tsum N
  have hsplit : ∀ x : ℝ≥0∞, x ^ p = x * x ^ (p - 1) := by
    intro x
    conv_lhs => rw [show p = 1 + (p - 1) by ring]
    rw [ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one]
  calc ∑' N, c N ^ p = ∑' N, c N * c N ^ (p - 1) := by
        congr 1; funext N; exact hsplit _
    _ ≤ ∑' N, c N * S ^ (p - 1) := by
        apply ENNReal.tsum_le_tsum; intro N
        exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hle N) (by linarith))
    _ = S * S ^ (p - 1) := by rw [ENNReal.tsum_mul_right]
    _ = S ^ p := (hsplit S).symm

end CoarseDeGiorgi.Endpoint.Potential
