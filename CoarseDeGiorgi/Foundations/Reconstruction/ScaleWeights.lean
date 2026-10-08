import CoarseDeGiorgi.Foundations.Reconstruction.ScaleSummation
import CoarseDeGiorgi.Foundations.Reconstruction.AuxIncrementLp

/-! # Absolute-scale weights and the exact integer indexing -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Relative natural depth enumerates every integer scale above the root. -/
def reconstructionScaleEquiv (m : ℤ) : ℕ ≃ {k : ℤ // m ≤ k} where
  toFun := fun j => ⟨m + j, by omega⟩
  invFun := fun k => (k.1 - m).toNat
  left_inv := by intro j; simp only [add_sub_cancel_left, Int.toNat_natCast]
  right_inv := by
    intro k
    apply Subtype.ext
    dsimp only
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr k.2)]
    omega

/-- Reindexing introduces no omission or multiplicity in the source series. -/
theorem tsum_reconstructionScale_reindex (m : ℤ) (a : {k : ℤ // m ≤ k} → ℝ≥0∞) :
    (∑' k : {k : ℤ // m ≤ k}, a k) =
      ∑' j : ℕ, a ⟨m + j, by omega⟩ :=
  ((reconstructionScaleEquiv m).tsum_eq a).symm

/-- Physical lengths produce the required absolute integer weight. -/
theorem auxSide_fractional_weight (m k : ℤ) (α : ℝ) :
    (auxSide (m + k)) ^ (1 - α) =
      (3 : ℝ) ^ (1 - α) * (3 : ℝ) ^ (-((m + k : ℤ) : ℝ) * (1 - α)) := by
  unfold auxSide
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have heq : ((1 - (m + k) : ℤ) : ℝ) * (1 - α) =
      (1 - α) + (-((m + k : ℤ) : ℝ) * (1 - α)) := by
    simp only [Int.cast_sub, Int.cast_one]
    ring
  rw [heq, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

end

end CoarseDeGiorgi.Foundations.Reconstruction
