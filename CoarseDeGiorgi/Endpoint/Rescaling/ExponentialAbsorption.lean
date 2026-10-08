import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Fixed prefactors and contrast powers are absorbed in the endpoint exponential. -/

open scoped ENNReal

namespace CoarseDeGiorgi.Endpoint.Rescaling

theorem absorb_polynomial (F : ℝ≥0∞) (hF : F ≠ ⊤) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ≥0∞, T ≠ ⊤ → 1 ≤ T →
      F * T.rpow β ≤ ENNReal.ofReal (Real.exp (C * Real.sqrt T.toReal)) := by
  refine ⟨|Real.log F.toReal| + 2 * β, by positivity, ?_⟩
  intro T hT hT1
  by_cases hF0 : F = 0
  · simp [hF0]
  have hFpos : 0 < F.toReal := ENNReal.toReal_pos hF0 hF
  have hTr : 1 ≤ T.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hT hT1
  have hTp : 0 < T.toReal := zero_lt_one.trans_le hTr
  have hsqrt : 1 ≤ Real.sqrt T.toReal := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hTr
  have hlog : Real.log T.toReal ≤ 2 * Real.sqrt T.toReal := by
    have h := Real.log_le_self (Real.sqrt_nonneg T.toReal)
    rw [Real.log_sqrt ENNReal.toReal_nonneg] at h
    linarith only [h]
  have hlogF : Real.log F.toReal ≤ |Real.log F.toReal| * Real.sqrt T.toReal :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hsqrt)
  have hlogT := mul_le_mul_of_nonneg_left hlog hβ
  have hexp : F.toReal * Real.rpow T.toReal β ≤
      Real.exp ((|Real.log F.toReal| + 2 * β) * Real.sqrt T.toReal) := by
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hTp, ← Real.exp_log hFpos, ← Real.exp_add]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith only [hlogF, hlogT]
  have heF : F = ENNReal.ofReal F.toReal := (ENNReal.ofReal_toReal hF).symm
  have heT : T = ENNReal.ofReal T.toReal := (ENNReal.ofReal_toReal hT).symm
  conv_lhs => rw [heF, heT, ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hTp,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.rpow_eq_pow] using hexp)

end CoarseDeGiorgi.Endpoint.Rescaling
