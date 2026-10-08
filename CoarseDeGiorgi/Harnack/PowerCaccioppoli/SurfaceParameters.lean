module

public import CoarseDeGiorgi.Harnack.PowerCaccioppoli.SurfaceArithmetic
public import CoarseDeGiorgi.Statements.IsTriadicWidth

/-! # Parameters and width spelling for the power surface estimate -/

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open scoped ENNReal

/-- `(c² M)^(1/2) = c M^(1/2)` in `ℝ≥0∞` for `c ≥ 0`. -/
theorem scaled_moment_half_power {c : ℝ} (hc : 0 ≤ c) (M : ℝ≥0∞) :
    (ENNReal.ofReal (c ^ 2) * M) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal c * M ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_pow hc,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- A nonzero extended real raised to a nonpositive power is finite. -/
theorem ennreal_rpow_lt_top_of_nonpos {x : ℝ≥0∞} {y : ℝ}
    (hy : y ≤ 0) (hx : x ≠ 0) : x ^ y < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  rcases ENNReal.rpow_eq_top_iff.mp htop with ⟨hzero, _⟩ | ⟨_, hpos⟩
  · exact hx hzero
  · exact (not_lt_of_ge hy) hpos

/-- An integer power `3^k ≤ 1` is a triadic width. -/
theorem triadic_width_of_zpow_le_one {k : ℤ} (hk : (3 : ℝ) ^ k ≤ 1) :
    IsTriadicWidth ((3 : ℝ) ^ k) := by
  have hk0 : k ≤ 0 := (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hk
  refine ⟨(-k).toNat, ?_⟩
  have he : -(((-k).toNat : ℕ) : ℤ) = k := by omega
  rw [he]

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
