import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

namespace CoarseDeGiorgi.Foundations.Iteration

open Filter

variable {X : ℕ → ℝ} {ω : ℝ}

theorem geometric_decay_from (hω : 0 ≤ ω)
    (hstep : ∀ n, X (n + 1) ≤ ω * X n) (n k : ℕ) :
    X (n + k) ≤ ω ^ k * X n := by
  induction k with
  | zero => simp only [Nat.add_zero, pow_zero, one_mul, le_refl]
  | succ k ih =>
    calc
      X (n + (k + 1)) ≤ ω * X (n + k) := hstep (n + k)
      _ ≤ ω * (ω ^ k * X n) := mul_le_mul_of_nonneg_left ih hω
      _ = ω ^ (k + 1) * X n := by rw [pow_succ']; ac_rfl

theorem geometric_decay (hω : 0 ≤ ω) (hstep : ∀ n, X (n + 1) ≤ ω * X n) (n : ℕ) :
    X n ≤ ω ^ n * X 0 := by
  simpa only [Nat.zero_add] using geometric_decay_from hω hstep 0 n

end CoarseDeGiorgi.Foundations.Iteration
