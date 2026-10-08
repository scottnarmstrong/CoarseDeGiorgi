import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ENNReal lemmas for the cubical comparison
-/

open scoped ENNReal

namespace CoarseDeGiorgi.Cubical

/-- `(∑ x_l)^{1/2} ≤ ∑ x_l^{1/2}` in `ℝ≥0∞`. -/
theorem tsum_rpow_half_le {ι : Type*} (x : ι → ℝ≥0∞) :
    (∑' l, x l) ^ ((1 : ℝ) / 2) ≤ ∑' l, (x l) ^ ((1 : ℝ) / 2) := by
  set y : ι → ℝ≥0∞ := fun l => (x l) ^ ((1 : ℝ) / 2) with hy
  have hxy : ∀ l, x l = y l * y l := by
    intro l
    simp only [hy]
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have h1 : ∑' l, x l ≤ (∑' l, y l) * (∑' l, y l) := by
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [hxy i, ← ENNReal.tsum_mul_left]
    exact ENNReal.le_tsum (f := fun j => y i * y j) i
  calc (∑' l, x l) ^ ((1 : ℝ) / 2)
      ≤ ((∑' l, y l) * (∑' l, y l)) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = ∑' l, y l := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num

/-- Geometric series with ratio `3^{-δ}`, `δ > 0`, is finite. -/
theorem tsum_geom_three_ne_top {δ : ℝ} (hδ : 0 < δ) :
    ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * δ))) ≠ ⊤ := by
  have hr : Real.rpow 3 (-δ) < 1 := by
    show (3 : ℝ) ^ (-δ) < 1
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ l : ℕ, Real.rpow 3 (-((l : ℝ) * δ)) = (Real.rpow 3 (-δ)) ^ l := by
    intro l
    show (3 : ℝ) ^ (-((l : ℝ) * δ)) = ((3 : ℝ) ^ (-δ)) ^ l
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have hs : ∑' l : ℕ, ENNReal.ofReal (Real.rpow 3 (-((l : ℝ) * δ))) =
      ∑' l : ℕ, (ENNReal.ofReal (Real.rpow 3 (-δ))) ^ l := by
    refine tsum_congr fun l => ?_
    rw [hpow l]
    exact ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) l
  rw [hs, ENNReal.tsum_geometric]
  have : ENNReal.ofReal (Real.rpow 3 (-δ)) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hr
  have h2 : (1 : ℝ≥0∞) - ENNReal.ofReal (Real.rpow 3 (-δ)) ≠ 0 :=
    (tsub_pos_of_lt this).ne'
  exact ENNReal.inv_ne_top.2 h2

end CoarseDeGiorgi.Cubical
