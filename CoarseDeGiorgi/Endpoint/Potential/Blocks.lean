import CoarseDeGiorgi.Endpoint.Potential.Sums

namespace CoarseDeGiorgi.Endpoint.Potential

open Finset
open scoped ENNReal

theorem three_rpow_split_le (g : ℝ) {k N : ℕ} (h : k ≤ N) :
    (3 : ℝ) ^ (g * k) = 3 ^ (g * N) * (3 ^ (-g)) ^ (N - k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast [Nat.cast_sub h]
  ring

theorem three_rpow_split_gt (g₁ g₂ : ℝ) {k N : ℕ} (h : N < k) :
    (3 : ℝ) ^ ((g₁ + g₂) * ((N : ℝ) + 1)) * 3 ^ (-((k : ℝ) * g₂)) =
      3 ^ (g₁ + g₂) * 3 ^ (g₁ * N) * (3 ^ (-g₂)) ^ (k - N) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num),
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast [Nat.cast_sub h.le]
  ring

theorem ofReal_three_rpow_split_le (g : ℝ) {k N : ℕ} (h : k ≤ N) :
    ENNReal.ofReal ((3 : ℝ) ^ (g * k)) =
      ENNReal.ofReal (3 ^ (g * N)) * ENNReal.ofReal (3 ^ (-g)) ^ (N - k) := by
  rw [three_rpow_split_le g h, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]

theorem ofReal_three_rpow_split_gt (g₁ g₂ : ℝ) {k N : ℕ} (h : N < k) :
    ENNReal.ofReal ((3 : ℝ) ^ ((g₁ + g₂) * ((N : ℝ) + 1))) *
        ENNReal.ofReal (3 ^ (-((k : ℝ) * g₂))) =
      ENNReal.ofReal (3 ^ (g₁ + g₂)) * ENNReal.ofReal (3 ^ (g₁ * N)) *
        ENNReal.ofReal (3 ^ (-g₂)) ^ (k - N) := by
  rw [← ENNReal.ofReal_mul (by positivity), three_rpow_split_gt g₁ g₂ h,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]

/-- Step 2 of the endpoint argument: the block bounds, summed at scale `N`, give `c_N`. -/
theorem blocks_bound (b α β : ℕ → ℝ≥0∞) (Eh : ℝ≥0∞) {C₀ g₁ g₂ : ℝ} (hC₀ : 0 ≤ C₀)
    (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂)
    (hα : ∀ k, 1 ≤ k → α k ≤ ENNReal.ofReal C₀ * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * k)) * b k * Eh)
    (hβ : ∀ k, 1 ≤ k →
      β k ≤ ENNReal.ofReal C₀ * ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * g₂))) * b k * Eh)
    (N : ℕ) (Θ : ℝ≥0∞) (hΘ : Θ ≤ ENNReal.ofReal ((3 : ℝ) ^ ((g₁ + g₂) * ((N : ℝ) + 1)))) :
    ∑ k ∈ Icc 1 N, α k + Θ * ∑' k, (if N < k then β k else 0) ≤
      ENNReal.ofReal (C₀ * 3 ^ (g₁ + g₂)) * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * Eh *
        scaleSum (ENNReal.ofReal (3 ^ (-g₁))) (ENNReal.ofReal (3 ^ (-g₂))) b N := by
  set Λ : ℝ≥0∞ := ENNReal.ofReal (C₀ * 3 ^ (g₁ + g₂)) * ENNReal.ofReal ((3 : ℝ) ^ (g₁ * N)) * Eh
    with hΛ
  have h3 : (1 : ℝ) ≤ 3 ^ (g₁ + g₂) := Real.one_le_rpow (by norm_num) (by linarith)
  have hC : ENNReal.ofReal C₀ ≤ ENNReal.ofReal (C₀ * 3 ^ (g₁ + g₂)) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  unfold scaleSum
  rw [mul_add]
  have hA : ∑ k ∈ Icc 1 N, α k ≤
      ∑ k ∈ Icc 1 N, Λ * (ENNReal.ofReal (3 ^ (-g₁)) ^ (N - k) * b k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_Icc.1 hk
    refine (hα k hk'.1).trans ?_
    rw [ofReal_three_rpow_split_le g₁ hk'.2, hΛ]
    calc _ ≤ ENNReal.ofReal (C₀ * 3 ^ (g₁ + g₂)) * (ENNReal.ofReal (3 ^ (g₁ * N)) *
            ENNReal.ofReal (3 ^ (-g₁)) ^ (N - k)) * b k * Eh := by gcongr
      _ = _ := by ring
  have hB : Θ * ∑' k, (if N < k then β k else 0) ≤
      ∑' k, Λ * (if N < k then ENNReal.ofReal (3 ^ (-g₂)) ^ (k - N) * b k else 0) := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : N < k
    · simp only [hk, ite_true]
      have hk1 : 1 ≤ k := by omega
      calc Θ * β k ≤ ENNReal.ofReal ((3 : ℝ) ^ ((g₁ + g₂) * ((N : ℝ) + 1))) *
              (ENNReal.ofReal C₀ * ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * g₂))) * b k * Eh) :=
            mul_le_mul' hΘ (hβ k hk1)
        _ = ENNReal.ofReal C₀ * (ENNReal.ofReal ((3 : ℝ) ^ ((g₁ + g₂) * ((N : ℝ) + 1))) *
              ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * g₂)))) * b k * Eh := by ring
        _ = ENNReal.ofReal C₀ * (ENNReal.ofReal (3 ^ (g₁ + g₂)) * ENNReal.ofReal (3 ^ (g₁ * N)) *
              ENNReal.ofReal (3 ^ (-g₂)) ^ (k - N)) * b k * Eh := by
            rw [ofReal_three_rpow_split_gt g₁ g₂ hk]
        _ ≤ _ := by
            rw [hΛ, ENNReal.ofReal_mul hC₀]
            apply le_of_eq
            ring
    · simp [hk]
  calc _ ≤ _ := add_le_add hA hB
    _ = _ := by
      rw [← Finset.mul_sum, ENNReal.tsum_mul_left, ← mul_add]

end CoarseDeGiorgi.Endpoint.Potential
