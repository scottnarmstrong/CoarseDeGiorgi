import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Constant absorption for the completion of Theorem C. -/

namespace CoarseDeGiorgi.Endpoint

/-- The polynomial contrast and the two fixed prefactors fit in one exponential. -/
theorem completion_absorption {A D B H X : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hH : 0 ≤ H) (hX : 1 ≤ X) :
    A * X * Real.exp (B * Real.sqrt X) + D * Real.exp (H * Real.sqrt X) ≤
      Real.exp ((A + D + B + H + 2) * Real.sqrt X) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hs : 1 ≤ Real.sqrt X := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hX
  have hAD : 0 ≤ A + D := add_nonneg hA hD
  have hpref : A + D ≤ Real.exp ((A + D) * Real.sqrt X) :=
    (le_add_of_nonneg_right zero_le_one).trans
      ((Real.add_one_le_exp (A + D)).trans
        (Real.exp_le_exp.mpr (le_mul_of_one_le_right hAD hs)))
  have hroot : Real.sqrt X ≤ Real.exp (Real.sqrt X) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hpoly : X ≤ Real.exp (2 * Real.sqrt X) := by
    calc
      X = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0).symm
      _ ≤ Real.exp (Real.sqrt X) * Real.exp (Real.sqrt X) :=
        mul_le_mul hroot hroot (Real.sqrt_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * Real.sqrt X) := by rw [← Real.exp_add]; congr 1; ring
  have hBE : Real.exp (B * Real.sqrt X) ≤ Real.exp ((B + H) * Real.sqrt X) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hH)
      (Real.sqrt_nonneg _))
  have hHE : Real.exp (H * Real.sqrt X) ≤ Real.exp ((B + H) * Real.sqrt X) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB)
      (Real.sqrt_nonneg _))
  calc
    _ ≤ A * X * Real.exp ((B + H) * Real.sqrt X) +
        D * X * Real.exp ((B + H) * Real.sqrt X) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hBE (mul_nonneg hA hX0)
      · exact mul_le_mul (le_mul_of_one_le_right hD hX) hHE
          (Real.exp_pos _).le (mul_nonneg hD hX0)
    _ = (A + D) * X * Real.exp ((B + H) * Real.sqrt X) := by ring
    _ ≤ Real.exp ((A + D) * Real.sqrt X) * Real.exp (2 * Real.sqrt X) *
        Real.exp ((B + H) * Real.sqrt X) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hpref hpoly hX0 (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end CoarseDeGiorgi.Endpoint
