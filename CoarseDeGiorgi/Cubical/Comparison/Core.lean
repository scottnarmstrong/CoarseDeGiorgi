import CoarseDeGiorgi.Cubical.Comparison.Basic

/-!
# The geometric-tail summation behind Proposition `p.cubical.simplicial.equivalence`
-/

open scoped ENNReal

namespace CoarseDeGiorgi.Cubical

/-- `3^{-(k s)} 3^{-(l η)} = 3^{-((k+l) s)} 3^{-(l (η - s))}` as `ℝ≥0∞`. -/
theorem three_weight_split (k l : ℕ) (s η : ℝ) :
    ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * η))) =
      ENNReal.ofReal (Real.rpow 3 (-(((k + l : ℕ) : ℝ) * s))) *
        ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (η - s)))) := by
  have h : ∀ x y : ℝ, ENNReal.ofReal (Real.rpow 3 x) * ENNReal.ofReal (Real.rpow 3 y) =
      ENNReal.ofReal (Real.rpow 3 (x + y)) := by
    intro x y
    show ENNReal.ofReal ((3 : ℝ) ^ x) * ENNReal.ofReal ((3 : ℝ) ^ y) = ENNReal.ofReal ((3 : ℝ) ^ (x + y))
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) x)]
    congr 1
    exact (Real.rpow_add (by norm_num) x y).symm
  rw [h, h]
  have e : -((k : ℝ) * s) + -((l : ℝ) * η) = -(((k + l : ℕ) : ℝ) * s) + -((l : ℝ) * (η - s)) := by
    push_cast; ring
  rw [e]

/-- Summation of geometric tails: if `B k ≤ K ∑_l 3^{-lη} Z (k+l)` then
`∑_k 3^{-ks} B k ≤ K (∑_l 3^{-l(η-s)}) ∑_m 3^{-ms} Z m`, for `s < η`. -/
theorem tail_sum_le (B Z : ℕ → ℝ≥0∞) (K : ℝ≥0∞) (s η : ℝ)
    (hB : ∀ k, B k ≤ K * ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * η))) * Z (k + l)) :
    ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * B k ≤
      K * ((∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (η - s))))) *
        ∑' m : ℕ, ENNReal.ofReal (Real.rpow 3 (-((m : ℝ) * s))) * Z m) := by
  set u : ℕ → ℝ≥0∞ := fun l => ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (η - s)))) with hu
  set T : ℝ≥0∞ := ∑' m : ℕ, ENNReal.ofReal (Real.rpow 3 (-((m : ℝ) * s))) * Z m with hT
  have step : ∀ k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * B k ≤
      K * ∑' l : ℕ, u l * (ENNReal.ofReal (Real.rpow 3 (-(((k + l : ℕ) : ℝ) * s))) * Z (k + l)) := by
    intro k
    calc ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * B k
        ≤ ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
            (K * ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * η))) * Z (k + l)) :=
          by gcongr; exact hB k
      _ = K * ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
            (ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * η))) * Z (k + l)) := by
          rw [ENNReal.tsum_mul_left, mul_left_comm]
      _ = K * ∑' l : ℕ, u l * (ENNReal.ofReal (Real.rpow 3 (-(((k + l : ℕ) : ℝ) * s))) * Z (k + l)) := by
          congr 1
          refine tsum_congr fun l => ?_
          rw [← mul_assoc, three_weight_split k l s η, mul_assoc, mul_comm]
          simp only [hu]
          ring
  have tail : ∀ l : ℕ, ∑' k : ℕ, (ENNReal.ofReal (Real.rpow 3 (-(((k + l : ℕ) : ℝ) * s))) * Z (k + l)) ≤ T := by
    intro l
    have hinj : Function.Injective (fun k : ℕ => k + l) := fun a b h => by simpa using h
    exact ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun m : ℕ => ENNReal.ofReal (Real.rpow 3 (-((m : ℝ) * s))) * Z m)
  calc ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * B k
      ≤ ∑' k : ℕ, K * ∑' l : ℕ, u l *
          (ENNReal.ofReal (Real.rpow 3 (-(((k + l : ℕ) : ℝ) * s))) * Z (k + l)) :=
        ENNReal.tsum_le_tsum step
    _ = K * ∑' l : ℕ, u l * ∑' k : ℕ,
          (ENNReal.ofReal (Real.rpow 3 (-(((k + l : ℕ) : ℝ) * s))) * Z (k + l)) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        congr 1
        refine tsum_congr fun l => ?_
        rw [ENNReal.tsum_mul_left]
    _ ≤ K * ∑' l : ℕ, u l * T := by
        gcongr with l
        exact tail l
    _ = K * ((∑' l : ℕ, u l) * T) := by rw [ENNReal.tsum_mul_right]

end CoarseDeGiorgi.Cubical
