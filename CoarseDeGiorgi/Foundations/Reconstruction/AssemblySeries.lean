module

public import CoarseDeGiorgi.Foundations.Reconstruction.ScaleWeights

/-! # Geometric collapse and absolute-scale normalization of reconstruction -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The relative block lengths are exactly the absolute auxiliary side lengths. -/
theorem assembly_length_rpow (m : ℤ) (j : ℕ) (q : ℝ) :
    auxSide (m + j) ^ q = (3 : ℝ) ^ ((1 - (m : ℝ) - (j : ℝ)) * q) := by
  unfold auxSide
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- This identity supplies the exact geometric decay when the sums are reversed. -/
theorem assembly_tail_weight (m : ℤ) (α : ℝ) {j k : ℕ} (hjk : j ≤ k) :
    ENNReal.ofReal (auxSide (m + j) ^ (-α)) *
        ENNReal.ofReal (auxSide (m + k)) =
      ENNReal.ofReal ((3 : ℝ) ^ (-α)) ^ (k - j) *
        ENNReal.ofReal (auxSide (m + k) ^ (1 - α)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (auxSide_pos _).le _),
    ← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _), ← ENNReal.ofReal_mul (pow_nonneg
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) _)]
  congr 1
  have hk : auxSide (m + k) = (3 : ℝ) ^ (1 - (m : ℝ) - (k : ℝ)) := by
    simpa only [Real.rpow_one, mul_one] using assembly_length_rpow m k 1
  rw [assembly_length_rpow, assembly_length_rpow, hk,
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Nat.cast_sub hjk]
  congr 1
  ring

/-- Tonelli and geometric summation, retaining the original unaveraged `L^1` scope. -/
theorem assembly_weighted_tails_le (m : ℤ) (α : ℝ) (A : ℕ → ℝ≥0∞) :
    (∑' j : ℕ, ENNReal.ofReal (auxSide (m + j) ^ (-α)) *
      ∑' k : ℕ, if j ≤ k then ENNReal.ofReal (auxSide (m + k)) * A k else 0) ≤
      (1 - ENNReal.ofReal ((3 : ℝ) ^ (-α)))⁻¹ *
        ∑' k : ℕ, ENNReal.ofReal (auxSide (m + k) ^ (1 - α)) * A k := by
  have heq :
      (∑' j : ℕ, ENNReal.ofReal (auxSide (m + j) ^ (-α)) *
        ∑' k : ℕ, if j ≤ k then ENNReal.ofReal (auxSide (m + k)) * A k else 0) =
      ∑' j : ℕ, ∑' k : ℕ, if j ≤ k then
        ENNReal.ofReal ((3 : ℝ) ^ (-α)) ^ (k - j) *
          (ENNReal.ofReal (auxSide (m + k) ^ (1 - α)) * A k) else 0 := by
    apply tsum_congr
    intro j
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    split_ifs with hjk
    · rw [← mul_assoc, assembly_tail_weight m α hjk, mul_assoc]
    · exact mul_zero _
  rw [heq]
  exact tsum_geometric_tails_le _ _

theorem assembly_geometric_constant_ne_top {α : ℝ} (hα : 0 < α) :
    (1 - ENNReal.ofReal ((3 : ℝ) ^ (-α)))⁻¹ ≠ ∞ := by
  apply geometric_tail_constant_ne_top
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hα))

/-- Step 11: reflection multiplicity and physical side lengths leave just a uniform factor. -/
theorem assembly_absolute_series {d : ℕ} (m : ℤ) (z : Fin d → ℤ)
    (Dw : Vec d → Vec d) (α r : ℝ) :
    (∑' k : ℕ, ENNReal.ofReal (auxSide (m + k) ^ (1 - α)) *
      (((2 : ℝ≥0∞) ^ d) ^ (1 / r) *
        eLpNorm (fun x => CoarseDeGiorgi.euclidNorm
          (CoarseDeGiorgi.auxAverage m (m + k) z Dw x))
          (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)))) =
      (ENNReal.ofReal ((3 : ℝ) ^ (1 - α)) * ((2 : ℝ≥0∞) ^ d) ^ (1 / r)) *
        ∑' k : {k : ℤ // m ≤ k},
          ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
            eLpNorm (fun x => CoarseDeGiorgi.euclidNorm
              (CoarseDeGiorgi.auxAverage m k.1 z Dw x))
              (ENNReal.ofReal r) (volume.restrict (CoarseDeGiorgi.auxCube m z)) := by
  rw [tsum_reconstructionScale_reindex, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [auxSide_fractional_weight, ENNReal.ofReal_mul
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
  ac_rfl

end
end CoarseDeGiorgi.Foundations.Reconstruction
