module

public import CoarseDeGiorgi.Selection.SourceRadius
public import CoarseDeGiorgi.Selection.TraceTransport
public import CoarseDeGiorgi.Selection.SurfaceMeasurability

@[expose] public section

namespace CoarseDeGiorgi.Selection

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Moving Lᵖ trace norms are measurable for every positive finite exponent. -/
theorem measurable_surface_eLpNorm {n : ℕ} {F : Vec (n + 1) → ℝ}
    (hF : Measurable F) {r : ℝ} (hr : 0 < r) :
    Measurable (fun τ => eLpNorm F (ENNReal.ofReal r) (CoarseDeGiorgi.surfaceMeasure τ)) := by
  have he (τ : ℝ) : eLpNorm F (ENNReal.ofReal r) (CoarseDeGiorgi.surfaceMeasure τ) =
      (∫⁻ x, ENNReal.ofReal (|F x| ^ r) ∂CoarseDeGiorgi.surfaceMeasure τ) ^ (1 / r) := by
    rw [← Foundations.FracGeometry.eLpNorm_ofReal_rpow hr hF,
      ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]
  simp_rw [he]
  exact (measurable_surfaceIntegral (by fun_prop)).pow_const _

end

end CoarseDeGiorgi.Selection
