import CoarseDeGiorgi.Statements.LowerMoment
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Finite and vanishing tails of the reconstruction costs -/
namespace CoarseDeGiorgi.Endpoint.Reconstruction
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology BigOperators
noncomputable section

def blockCost {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (q : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ (-(k : ℤ))) *
    (ENNReal.ofReal (lowerCellAverage a ha k q)) ^ (1 / (2 * q))

def blockTail (c : ℕ → ℝ≥0∞) (N : ℕ) : ℝ≥0∞ := ∑' k, if N < k then c k else 0

theorem blockTail_eq_shift (c : ℕ → ℝ≥0∞) (N : ℕ) :
    blockTail c N = ∑' j, c (j + (N + 1)) := by
  have h := Summable.sum_add_tsum_nat_add' (f := fun k => if N < k then c k else 0)
    (k := N + 1) ENNReal.summable
  have hzero : (∑ k ∈ Finset.range (N + 1), if N < k then c k else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [show ¬N < k by omega]
  simpa only [blockTail, hzero, zero_add, show ∀ j : ℕ, N < j + (N + 1) from fun j => by omega,
    ite_true] using h.symm

theorem blockTail_ne_top {c : ℕ → ℝ≥0∞} (hc : ∑' k, c k ≠ ⊤) (N : ℕ) :
    blockTail c N ≠ ⊤ := by
  apply ne_top_of_le_ne_top hc
  exact ENNReal.tsum_le_tsum fun k => by split_ifs <;> simp

theorem tendsto_blockTail {c : ℕ → ℝ≥0∞} (hc : ∑' k, c k ≠ ⊤) :
    Tendsto (blockTail c) atTop (𝓝 0) := by
  change Tendsto (fun N => blockTail c N) atTop (𝓝 0)
  simp_rw [blockTail_eq_shift]
  exact (ENNReal.tendsto_sum_nat_add c hc).comp (tendsto_add_atTop_nat 1)

theorem sum_Icc_le_blockTail (c : ℕ → ℝ≥0∞) (N M : ℕ) :
    ∑ k ∈ Finset.Icc (N + 1) M, c k ≤ blockTail c N := by
  have h := ENNReal.sum_le_tsum (f := fun k => if N < k then c k else 0)
    (Finset.Icc (N + 1) M)
  change _ ≤ blockTail c N at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [ite_eq_left (by have := (Finset.mem_Icc.mp hk).1; omega)]

theorem blockCost_tsum_ne_top {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {q t : ℝ}
    (hq : 1 < q) (ht : 0 < t) (ht1 : t < 1)
    (hl : 0 < lowerMoment a ha t q ht hq.le) : ∑' k, blockCost a ha q k ≠ ⊤ := by
  let b : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * t))) *
    (ENNReal.ofReal (lowerCellAverage a ha k q)) ^ (1 / (2 * q))
  have hp : 0 < ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) := by
    rw [ENNReal.ofReal_pos]
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hb : ∑' k, b k ≠ ⊤ := by
    intro htop
    unfold lowerMoment at hl
    change 0 < (ENNReal.ofReal (1 - (3 : ℝ) ^ (-t)) * ∑' k, b k).rpow (-2) at hl
    rw [htop, ENNReal.mul_top hp.ne', ENNReal.rpow_eq_pow, ENNReal.top_rpow_of_neg (by norm_num)] at hl
    exact (lt_irrefl _ hl)
  have hcost (k : ℕ) : blockCost a ha q k ≤ b k := by
    dsimp only [blockCost, b]
    apply mul_le_mul_of_nonneg_right _ (bot_le : (0 : ℝ≥0∞) ≤ _)
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.rpow_intCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num only [Int.cast_neg, Int.cast_natCast]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  exact ne_top_of_le_ne_top hb (ENNReal.tsum_le_tsum hcost)

end
end CoarseDeGiorgi.Endpoint.Reconstruction
