import CoarseDeGiorgi.Statements.EuclidNorm
import CoarseDeGiorgi.Statements.OriginCube
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The radial field of the weak Harnack sharpness example

The field is `a(ρ) = ρ^β log³(eR/ρ)` with `R = √d` and `β = 2t + d/q`.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- `R = √d`. -/
def whR (d : ℕ) : ℝ := Real.sqrt d

/-- The exponent `β = 2t + d/q`. -/
def whBeta (d : ℕ) (q t : ℝ) : ℝ := 2 * t + (d : ℝ) / q

/-- `log(eR/ρ)`. -/
def whLog (d : ℕ) (ρ : ℝ) : ℝ := 1 + Real.log (whR d) - Real.log ρ

/-- The radial profile `a(ρ) = ρ^β log³(eR/ρ)`. -/
def whA (d : ℕ) (q t : ℝ) (ρ : ℝ) : ℝ := ρ ^ whBeta d q t * whLog d ρ ^ 3

theorem whR_pos {d : ℕ} (hd : 1 ≤ d) : 0 < whR d := by
  unfold whR
  exact Real.sqrt_pos.2 (by exact_mod_cast hd)

theorem whR_sq {d : ℕ} : whR d ^ 2 = d := by
  unfold whR
  exact Real.sq_sqrt (Nat.cast_nonneg _)

theorem whLog_eq {d : ℕ} (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ) :
    whLog d ρ = Real.log (Real.exp 1 * whR d / ρ) := by
  unfold whLog
  rw [Real.log_div (mul_pos (Real.exp_pos 1) (whR_pos hd)).ne' hρ.ne',
    Real.log_mul (Real.exp_pos 1).ne' (whR_pos hd).ne', Real.log_exp]

theorem one_le_whLog {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hR : ρ ≤ whR d) :
    1 ≤ whLog d ρ := by
  unfold whLog
  have := Real.log_le_log hρ hR
  linarith

theorem whLog_anti {d : ℕ} {ρ σ : ℝ} (hρ : 0 < ρ) (hρσ : ρ ≤ σ) : whLog d σ ≤ whLog d ρ := by
  unfold whLog
  have := Real.log_le_log hρ hρσ
  linarith

theorem whA_pos {d : ℕ} {q t : ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hR : ρ ≤ whR d) : 0 < whA d q t ρ := by
  unfold whA
  have := one_le_whLog hρ hR
  exact mul_pos (Real.rpow_pos_of_pos hρ _) (pow_pos (by linarith) 3)

theorem whA_zero {d : ℕ} {q t : ℝ} (hβ : 0 < whBeta d q t) : whA d q t 0 = 0 := by
  unfold whA
  rw [Real.zero_rpow hβ.ne']
  simp

/-- The profile is bounded on `(0, R]`. -/
theorem whA_le {d : ℕ} (hd : 1 ≤ d) {q t : ℝ} (hβ : 0 < whBeta d q t) {ρ : ℝ} (hρ : 0 < ρ)
    (hR : ρ ≤ whR d) :
    whA d q t ρ ≤ (Real.exp 1 * whR d) ^ whBeta d q t / (whBeta d q t / 3) ^ 3 := by
  set β := whBeta d q t with hβdef
  have hγ : 0 < β / 3 := by positivity
  have hx : 0 < Real.exp 1 * whR d / ρ := div_pos (mul_pos (Real.exp_pos 1) (whR_pos hd)) hρ
  have h1 := Real.log_le_rpow_div hx.le hγ
  rw [← whLog_eq hd hρ] at h1
  have h0 : 0 ≤ whLog d ρ := by linarith [one_le_whLog hρ hR]
  have h3 : whLog d ρ ^ 3 ≤ ((Real.exp 1 * whR d / ρ) ^ (β / 3) / (β / 3)) ^ 3 :=
    pow_le_pow_left₀ h0 h1 3
  have h4 : ((Real.exp 1 * whR d / ρ) ^ (β / 3) / (β / 3)) ^ 3 =
      (Real.exp 1 * whR d / ρ) ^ β / (β / 3) ^ 3 := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 3
    push_cast; ring
  have h5 : ρ ^ β * ((Real.exp 1 * whR d / ρ) ^ β / (β / 3) ^ 3) =
      (Real.exp 1 * whR d) ^ β / (β / 3) ^ 3 := by
    rw [Real.div_rpow (mul_pos (Real.exp_pos 1) (whR_pos hd)).le hρ.le]
    field_simp
  unfold whA
  calc ρ ^ β * whLog d ρ ^ 3 ≤ ρ ^ β * ((Real.exp 1 * whR d / ρ) ^ β / (β / 3) ^ 3) := by
        rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hρ.le _)
    _ = _ := h5

end

end CoarseDeGiorgi.SharpnessExamples
