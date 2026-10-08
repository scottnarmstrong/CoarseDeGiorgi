module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Raising each ENNReal step to the reciprocal exponent gives its multiplicative
factor in the unpowered chain.
-/
private theorem finite_rpow_iteration_step
    (M K : ℕ → ℝ≥0∞) (p : ℕ → ℝ) (j : ℕ)
    (hpj : 0 < p j)
    (hstep : M (j + 1) ^ (p j) ≤ K j * M j ^ (p j)) :
    M (j + 1) ≤ K j ^ (1 / p j) * M j := by
  have hroot_nonneg : 0 ≤ 1 / p j := by positivity
  have hroot := ENNReal.rpow_le_rpow hstep hroot_nonneg
  calc
    M (j + 1) = (M (j + 1) ^ (p j)) ^ (1 / p j) := by
      rw [← ENNReal.rpow_mul]
      rw [one_div, mul_inv_cancel₀ (ne_of_gt hpj), ENNReal.rpow_one]
    _ ≤ (K j * M j ^ (p j)) ^ (1 / p j) := hroot
    _ = K j ^ (1 / p j) * M j := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hroot_nonneg]
      rw [← ENNReal.rpow_mul]
      rw [one_div, mul_inv_cancel₀ (ne_of_gt hpj), ENNReal.rpow_one]

/-- Finite ENNReal power bounds multiply along the chain with the reciprocal
exponents as the costs.
-/
theorem finite_rpow_iteration_chain_product
    (M K : ℕ → ℝ≥0∞) (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ j < n, 0 < p j)
    (hstep : ∀ j < n,
      M (j + 1) ^ (p j) ≤ K j * M j ^ (p j)) :
    M n ≤ (∏ j ∈ Finset.range n, K j ^ (1 / p j)) * M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlast := finite_rpow_iteration_step M K p n (hp n (by omega))
      (hstep n (by omega))
    have hprev := ih (fun j hj => hp j (by omega))
      (fun j hj => hstep j (by omega))
    calc
      M (n + 1) ≤ K n ^ (1 / p n) * M n := hlast
      _ ≤ K n ^ (1 / p n) *
          ((∏ j ∈ Finset.range n, K j ^ (1 / p j)) * M 0) := by gcongr
      _ = (∏ j ∈ Finset.range (n + 1), K j ^ (1 / p j)) * M 0 := by
        rw [Finset.prod_range_succ]
        ac_rfl

end CoarseDeGiorgi.Harnack.Iterations
