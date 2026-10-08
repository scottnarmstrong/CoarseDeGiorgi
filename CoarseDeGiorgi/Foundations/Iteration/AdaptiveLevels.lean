module

public import CoarseDeGiorgi.Foundations.Iteration.Decay
public import CoarseDeGiorgi.Foundations.Iteration.Dyadic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Iteration

open Filter Finset
open scoped Topology

theorem adaptive_increment_bounds {X b : ℕ → ℝ} {K M δ γ ω : ℝ}
    (hX : ∀ n, 0 ≤ X n) (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hdecay : ∀ n, X (n + 1) ≤ ω * X n) (hratio : (2 : ℝ) ^ γ * ω = 1 / 2)
    (hlevel : ∀ n, b (n + 1) = b n + K * M * (dyadicGap δ n) ^ (-γ) * X n)
    (n : ℕ) :
    0 ≤ b (n + 1) - b n ∧
      b (n + 1) - b n ≤ (K * M * (δ / 2) ^ (-γ) * X 0) * (1 / 2 : ℝ) ^ n := by
  have hg : 0 < (2 : ℝ) ^ γ := Real.rpow_pos_of_pos (by norm_num) γ
  have hω : 0 ≤ ω := by nlinarith only [hg, hratio]
  have hx := geometric_decay hω hdecay n
  have hcoef : 0 ≤ K * M * (dyadicGap δ n) ^ (-γ) :=
    mul_nonneg (mul_nonneg hK hM) (Real.rpow_pos_of_pos (dyadicGap_pos hδ n) _).le
  have heq : b (n + 1) - b n = K * M * (dyadicGap δ n) ^ (-γ) * X n := by
    rw [hlevel]
    ring
  rw [heq]
  refine ⟨mul_nonneg hcoef (hX n), ?_⟩
  calc
    K * M * (dyadicGap δ n) ^ (-γ) * X n ≤
        K * M * (dyadicGap δ n) ^ (-γ) * (ω ^ n * X 0) :=
      mul_le_mul_of_nonneg_left hx hcoef
    _ = (K * M * (δ / 2) ^ (-γ) * X 0) * (1 / 2 : ℝ) ^ n := by
      rw [dyadicGap_rpow hδ, ← hratio, mul_pow]
      ring

/-- The total adaptive level increase and its finite limiting level. -/
theorem adaptive_levels {X b : ℕ → ℝ} {K M δ γ ω : ℝ}
    (hX : ∀ n, 0 ≤ X n) (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hdecay : ∀ n, X (n + 1) ≤ ω * X n) (hratio : (2 : ℝ) ^ γ * ω = 1 / 2)
    (hlevel : ∀ n, b (n + 1) = b n + K * M * (dyadicGap δ n) ^ (-γ) * X n) :
    Monotone b ∧ Summable (fun n => b (n + 1) - b n) ∧
      (∑' n : ℕ, (b (n + 1) - b n)) ≤ 2 * K * M * (δ / 2) ^ (-γ) * X 0 ∧
      ∃ L : ℝ, Tendsto b atTop (𝓝 L) ∧
        L - b 0 = ∑' n : ℕ, (b (n + 1) - b n) ∧
        L ≤ b 0 + 2 * K * M * (δ / 2) ^ (-γ) * X 0 := by
  let C := K * M * (δ / 2) ^ (-γ) * X 0
  have hb := adaptive_increment_bounds hX hK hM hδ hdecay hratio hlevel
  have hg : Summable (fun n : ℕ => C * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left C
  have hs : Summable (fun n => b (n + 1) - b n) :=
    Summable.of_nonneg_of_le (fun n => (hb n).1) (fun n => (hb n).2) hg
  have hsum : (∑' n : ℕ, (b (n + 1) - b n)) ≤ 2 * K * M * (δ / 2) ^ (-γ) * X 0 := by
    calc
      (∑' n : ℕ, (b (n + 1) - b n)) ≤ ∑' n : ℕ, C * (1 / 2 : ℝ) ^ n :=
        hs.tsum_le_tsum (fun n => (hb n).2) hg
      _ = 2 * K * M * (δ / 2) ^ (-γ) * X 0 := by
        rw [tsum_mul_left, tsum_geometric_two]
        dsimp [C]
        ring
  refine ⟨monotone_nat_of_le_succ (fun n => by linarith only [(hb n).1]), hs, hsum,
    b 0 + ∑' n : ℕ, (b (n + 1) - b n), ?_, ?_, ?_⟩
  · have ht := hs.hasSum.tendsto_sum_nat.const_add (b 0)
    simpa only [sum_range_sub, add_sub_cancel] using ht
  · ring
  · linarith only [hsum]

end CoarseDeGiorgi.Foundations.Iteration
