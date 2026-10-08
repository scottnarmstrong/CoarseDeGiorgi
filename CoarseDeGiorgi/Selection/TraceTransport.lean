import CoarseDeGiorgi.Selection.SurfaceEnergy

namespace CoarseDeGiorgi.Selection

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Coarea transports any measurable a.e. property on the annulus to almost every surface.
This applies to localized representatives, truncation identities, and density order. -/
theorem surface_ae_of_annulus_ae {n : ℕ} {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {P : Vec (n + 1) → Prop} (hP : MeasurableSet {x | P x})
    (hgood : ∀ᵐ x ∂volume.restrict (cubicalAnnulus (n + 1) ρ R), P x) :
    ∀ᵐ τ ∂volume.restrict (Ioo ρ R), ∀ᵐ x ∂CoarseDeGiorgi.surfaceMeasure τ, P x := by
  let g := {x | ¬P x}.indicator (fun _ => (1 : ℝ≥0∞))
  have hg : Measurable g := measurable_const.indicator hP.compl
  have hbulk : ∫⁻ x in cubicalAnnulus (n + 1) ρ R, g x = 0 :=
    lintegral_eq_zero_of_ae_eq_zero (hgood.mono (fun x hx => by simp [g, hx]))
  have hrad : ∫⁻ τ in Ioo ρ R, ∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ = 0 := by
    rw [cubical_coarea hρ hg, hbulk, mul_zero]
  have hae := (lintegral_eq_zero_iff (measurable_surfaceIntegral hg)).mp hrad
  filter_upwards [hae] with τ hτ
  rw [ae_iff]
  have he : (∫⁻ x, g x ∂CoarseDeGiorgi.surfaceMeasure τ) =
      CoarseDeGiorgi.surfaceMeasure τ {x | ¬P x} := by
    have hnot : MeasurableSet {x | ¬P x} := hP.compl
    dsimp only [g]
    rw [lintegral_indicator_const hnot, one_mul]
  exact he.symm.trans hτ




end

end CoarseDeGiorgi.Selection
