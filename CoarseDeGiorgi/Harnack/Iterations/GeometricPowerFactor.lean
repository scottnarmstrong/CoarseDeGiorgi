import CoarseDeGiorgi.Harnack.Iterations.SmallMomentStep

namespace CoarseDeGiorgi.Harnack.Iterations

/-- The contrast inequality `p² Θ ≤ c²` controls both geometric endpoint branches. On the
positive branch the input is stopped below r/4.
-/
theorem geometric_signed_powerFactor_bound {p c Θ r χ z : ℝ} (j : ℕ)
    (hp : 0 < p) (hc : 0 ≤ c) (hr : 0 < r) (_hΘ : 0 ≤ Θ)
    (hχ : 0 < χ) (hpc : p ^ 2 * Θ ≤ c ^ 2) (hcsmall : 2 * c < r)
    (hz : (z = p * χ ^ j ∧ z < r / 4) ∨ z = -(p * χ ^ j)) :
    z < r / 2 ∧ powerFactor (z / r) ^ 2 * Θ ≤ χ ^ (2 * j) := by
  have hden : r / 2 ≤ r - 2 * z := by
    rcases hz with ⟨_, hstop⟩ | hneg
    · linarith
    · rw [hneg]
      have hpos := mul_pos hp (pow_pos hχ j)
      linarith
  have hzhalf : z < r / 2 := by linarith
  have hdenpos : 0 < r - 2 * z := (by positivity : 0 < r / 2).trans_le hden
  have hnum : z ^ 2 * Θ ≤ c ^ 2 * χ ^ (2 * j) := by
    have heq : z ^ 2 = p ^ 2 * χ ^ (2 * j) := by
      rcases hz with ⟨hpos, _⟩ | hneg
      · rw [hpos, mul_pow, ← pow_mul, Nat.mul_comm]
      · rw [hneg, neg_sq, mul_pow, ← pow_mul, Nat.mul_comm]
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hpc (pow_nonneg hχ.le (2 * j))]
  have hcsq : c ^ 2 ≤ (r / 2) ^ 2 := by nlinarith
  have hdensq : (r / 2) ^ 2 ≤ (r - 2 * z) ^ 2 :=
    (sq_le_sq₀ (by positivity) hdenpos.le).2 hden
  refine ⟨hzhalf, ?_⟩
  rw [powerFactor_scaled_sq hr hzhalf, div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hdenpos)).2
  calc
    z ^ 2 * Θ ≤ c ^ 2 * χ ^ (2 * j) := hnum
    _ ≤ (r - 2 * z) ^ 2 * χ ^ (2 * j) :=
      mul_le_mul_of_nonneg_right (hcsq.trans hdensq) (by positivity)
    _ = _ := mul_comm _ _

end CoarseDeGiorgi.Harnack.Iterations
