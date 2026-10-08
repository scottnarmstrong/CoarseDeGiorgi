module

public import CoarseDeGiorgi.Selection.QuantitativeRadius
public import CoarseDeGiorgi.Selection.Sampling

@[expose] public section

namespace CoarseDeGiorgi.Selection

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem selectionInterval_subset {ρ R : ℝ} (_hgap : ρ < R) :
    selectionInterval ρ R ⊆ Ioo ρ R := by
  intro τ hτ
  change ρ + (R - ρ) / 4 < τ ∧ τ < ρ + (R - ρ) / 2 at hτ
  constructor <;> linarith

/-- Inverting the positive power in the implementation Lᵖ quantity is exact,
including infinite values. -/
theorem powerNorm_rpow {r : ℝ} (hr : 0 < r) (μ : Measure ℝ)
    (f : ℝ → ℝ≥0∞) :
    powerNorm r μ f ^ r = ∫⁻ τ, f τ ^ r ∂μ := by
  rw [powerNorm, ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]

end

end CoarseDeGiorgi.Selection
