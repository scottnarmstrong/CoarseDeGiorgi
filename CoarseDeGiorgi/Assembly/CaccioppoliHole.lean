import CoarseDeGiorgi.Assembly.CaccioppoliAbsorption
import CoarseDeGiorgi.Foundations.Iteration.HoleFilling

namespace CoarseDeGiorgi.Assembly

open MeasureTheory
open scoped ENNReal
open Foundations.Iteration

/-- The fixed source choice ε=2^(-κ-2) has geometric ratio one half. -/
theorem caccioppoli_hole_ratio (κ : ℝ) :
    (2 * (2 : ℝ) ^ (-κ - 2)) * (2 : ℝ) ^ κ = 1 / 2 := by
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have he : -κ - 2 + κ = -2 := by ring
  rw [he]
  norm_num

/-- Hole filling with the source's fixed ε and a real-valued forcing coefficient. -/
theorem caccioppoli_hole_filling {f : ℝ → ℝ≥0∞} (hf : Monotone f)
    {ρ R A κ : ℝ} (hρR : ρ < R) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hfinite : f R < ⊤)
    (hstep : ∀ ρ' R' : ℝ, ρ ≤ ρ' → ρ' < R' → R' ≤ R →
      f ρ' ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ (-κ - 2)) * f R' +
        ENNReal.ofReal (A * (R' - ρ') ^ (-κ))) :
    f ρ ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ κ) * ENNReal.ofReal A *
      ENNReal.ofReal ((R - ρ) ^ (-κ)) := by
  have hr := caccioppoli_hole_ratio κ
  have h := hole_filling_of_all_pairs hf hρR
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le hA hκ
    (by rw [hr]; norm_num) hfinite hstep
  rw [holeFillingConstant_of_half hr] at h
  exact h


end CoarseDeGiorgi.Assembly
