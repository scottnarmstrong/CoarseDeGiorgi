import CoarseDeGiorgi.Whitney.SeedArea

/-! # Algebra and order of the surface patch means -/

namespace CoarseDeGiorgi.Whitney

open Homogenization MeasureTheory Set
open scoped NNReal

noncomputable section

variable {d : ℕ}

theorem isCompact_seedSurface (τ : ℝ) : IsCompact (cubeSurface (d := d) τ) := by
  simpa only [cubeSurface, Metric.sphere, dist_zero_right] using
    isCompact_sphere (0 : Vec d) (τ / 2)

theorem seedSurface_integrable_of_continuousOn {τ : ℝ} (hτ : 0 ≤ τ)
    {f : Vec d → ℝ} (hf : ContinuousOn f (cubeSurface τ)) : Integrable f (surfaceMeasure τ) := by
  let := seedSurfaceMeasure_finite (d := d) τ
  have hi := hf.integrableOn_compact (μ := surfaceMeasure τ) (isCompact_seedSurface τ)
  apply hi.integrable_of_ae_notMem_eq_zero
  filter_upwards [show ∀ᵐ x ∂surfaceMeasure (d := d) τ, x ∈ cubeSurface τ from
    Foundations.FracGeometry.surfaceMeasure_ae_surface hτ] with x hx
  exact fun hn => (hn hx).elim

end

end CoarseDeGiorgi.Whitney

