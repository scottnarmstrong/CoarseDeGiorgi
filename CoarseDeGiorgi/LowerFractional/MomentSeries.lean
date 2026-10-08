module

public import CoarseDeGiorgi.LowerFractional.Aliases
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The lower spatial moment and its half series `e.lower.half.series`. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- Exact source identity, including the zero and infinite series cases. -/
theorem lower_moment_half_series {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (t q : ℝ)
    (ht : 0 < t) (hq : 1 ≤ q) :
    (lowerMoment a ha t q ht hq).rpow (-1 / 2) =
      ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)) := by
  unfold lowerMoment
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The normalizing factor is finite and strictly positive. -/
theorem lower_series_normalization_pos {t : ℝ} (ht : 0 < t) :
    0 < 1 - Real.rpow 3 (-t) := by
  apply sub_pos.mpr
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)

/-- Removing the normalizing factor is an equality, not a new series premise. -/
theorem lower_moment_series {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (t q : ℝ)
    (ht : 0 < t) (hq : 1 ≤ q) :
    (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
      (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) =
      ENNReal.ofReal ((1 - Real.rpow 3 (-t))⁻¹) *
        (lowerMoment a ha t q ht hq).rpow (-1 / 2) := by
  rw [lower_moment_half_series]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr
    (lower_series_normalization_pos ht).le), inv_mul_cancel₀
      (lower_series_normalization_pos ht).ne', ENNReal.ofReal_one, one_mul]



/-- The reconstruction-index tail is bounded by the actual natural-indexed
moment series; no extension to negative scales is assumed. -/
theorem lower_moment_tail_series {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (t q : ℝ)
    (ht : 0 < t) (hq : 1 ≤ q) (m : ℤ) (hm : 0 ≤ m) :
    (∑' k : {k : ℤ // m ≤ k},
      ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * t)) *
        (ENNReal.ofReal (lowerCellAverage a ha k.1.toNat q)) ^ (1 / (2 * q))) ≤
      ENNReal.ofReal ((1 - Real.rpow 3 (-t))⁻¹) *
        (lowerMoment a ha t q ht hq).rpow (-1 / 2) := by
  let i : {k : ℤ // m ≤ k} → ℕ := fun k => k.1.toNat
  have hi : Function.Injective i := by
    intro k l h
    apply Subtype.ext
    have hk : 0 ≤ k.1 := hm.trans k.2
    have hl : 0 ≤ l.1 := hm.trans l.2
    simpa only [i, Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hl] using
      congrArg (fun n : ℕ => (n : ℤ)) h
  rw [← lower_moment_series]
  convert ENNReal.tsum_comp_le_tsum_of_injective hi (fun k : ℕ =>
    ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * t))) *
      (ENNReal.ofReal (lowerCellAverage a ha k q)) ^ (1 / (2 * q))) using 1
  congr 1
  funext k
  have hk : ((k.1.toNat : ℕ) : ℝ) = (k.1 : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hm.trans k.2)
  dsimp [i]
  rw [hk, neg_mul]


end CoarseDeGiorgi.LowerFractional
