import CoarseDeGiorgi.Cubical.Comparison.Core

/-!
# Comparison of the weighted sums of Proposition `p.cubical.simplicial.equivalence`

For sequences `X, Y` of cell averages with the two-sided bound of Lemma `l.cubical.simplicial.moments`, compare the weighted sums
`∑ 3^{-ks} (X k)^{1/(2p)}` and `∑ 3^{-ks} (Y k)^{1/(2p)}`.
-/

open scoped ENNReal

namespace CoarseDeGiorgi.Cubical

theorem ofReal_rpow_three_half (l : ℕ) (θ : ℝ) :
    (ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * θ)))) ^ ((1 : ℝ) / 2) =
      ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (θ / 2)))) := by
  show (ENNReal.ofReal ((3 : ℝ) ^ (-((l : ℝ) * θ)))) ^ ((1 : ℝ) / 2) =
    ENNReal.ofReal ((3 : ℝ) ^ (-((l : ℝ) * (θ / 2))))
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (by norm_num)]
  congr 1
  show ((3 : ℝ) ^ (-((l : ℝ) * θ))) ^ ((1 : ℝ) / 2) = (3 : ℝ) ^ (-((l : ℝ) * (θ / 2)))
  rw [← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- Upper comparison of the weighted sums, given the upper half of Lemma `l.cubical.simplicial.moments`. -/
theorem sum_le_const_mul (p s C : ℝ) (hp : 1 < p) (_hs : 0 < s)
    (hsp : s < (1 / 2) * (1 - 1 / p)) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X Y : ℕ → ℝ),
      (∀ k, (ENNReal.ofReal (X k)) ^ (1 / p) ≤ ENNReal.ofReal C *
      ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
        (ENNReal.ofReal (Y (k + l))) ^ (1 / p)) →
      ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
          (ENNReal.ofReal (X k)) ^ (1 / (2 * p)) ≤
        ENNReal.ofReal K * ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
          (ENNReal.ofReal (Y k)) ^ (1 / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  set η : ℝ := (1 - 1 / p) / 2 with hη
  have hδ : 0 < η - s := by rw [hη]; linarith
  set G : ℝ≥0∞ := ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (η - s)))) with hG
  have hGtop : G ≠ ⊤ := tsum_geom_three_ne_top hδ
  have hG0 : G ≠ 0 := by
    intro h
    have := (ENNReal.tsum_eq_zero.1 h) 0
    simp at this
  set K0 : ℝ≥0∞ := (ENNReal.ofReal C) ^ ((1 : ℝ) / 2) * G with hK0
  have hK0top : K0 ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    ENNReal.ofReal_ne_top) hGtop
  have hK0z : K0 ≠ 0 := by
    refine mul_ne_zero ?_ hG0
    simp [hC]
  refine ⟨K0.toReal, ENNReal.toReal_pos hK0z hK0top, ?_⟩
  intro X Y h2
  rw [ENNReal.ofReal_toReal hK0top]
  have hB : ∀ k, (ENNReal.ofReal (X k)) ^ (1 / (2 * p)) ≤ (ENNReal.ofReal C) ^ ((1 : ℝ) / 2) *
      ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * η))) *
        (ENNReal.ofReal (Y (k + l))) ^ (1 / (2 * p)) := by
    intro k
    have e : (1 : ℝ) / (2 * p) = 1 / p * ((1 : ℝ) / 2) := by field_simp
    calc (ENNReal.ofReal (X k)) ^ (1 / (2 * p))
        = ((ENNReal.ofReal (X k)) ^ (1 / p)) ^ ((1 : ℝ) / 2) := by
          rw [← ENNReal.rpow_mul, e]
      _ ≤ (ENNReal.ofReal C * ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
            (ENNReal.ofReal (Y (k + l))) ^ (1 / p)) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow (h2 k) (by norm_num)
      _ = (ENNReal.ofReal C) ^ ((1 : ℝ) / 2) * (∑' l : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
              (ENNReal.ofReal (Y (k + l))) ^ (1 / p)) ^ ((1 : ℝ) / 2) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ (ENNReal.ofReal C) ^ ((1 : ℝ) / 2) * ∑' l : ℕ,
            (ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * (1 - 1 / p)))) *
              (ENNReal.ofReal (Y (k + l))) ^ (1 / p)) ^ ((1 : ℝ) / 2) := by
          gcongr
          exact tsum_rpow_half_le _
      _ = (ENNReal.ofReal C) ^ ((1 : ℝ) / 2) * ∑' l : ℕ,
            ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * η))) *
              (ENNReal.ofReal (Y (k + l))) ^ (1 / (2 * p)) := by
          congr 1
          refine tsum_congr fun l => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_rpow_three_half,
            ← ENNReal.rpow_mul, e]
  have := tail_sum_le (fun k => (ENNReal.ofReal (X k)) ^ (1 / (2 * p)))
    (fun k => (ENNReal.ofReal (Y k)) ^ (1 / (2 * p))) ((ENNReal.ofReal C) ^ ((1 : ℝ) / 2)) s η hB
  rw [hK0, mul_assoc]
  exact this

end CoarseDeGiorgi.Cubical
