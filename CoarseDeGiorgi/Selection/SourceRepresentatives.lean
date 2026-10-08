module

public import CoarseDeGiorgi.Selection.SourceResponses
public import CoarseDeGiorgi.Localization.SourceCover

@[expose] public section

namespace CoarseDeGiorgi.Selection
open Homogenization MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Coarea transports an arbitrary ambient a.e. property. A measurable null
superset removes the need to assume measurable source representatives. -/
theorem source_surface_ae_of_annulus_ae {n : ℕ} {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {P : Vec (n + 1) → Prop}
    (hgood : ∀ᵐ x ∂volume.restrict (cubicalAnnulus (n + 1) ρ R), P x) :
    ∀ᵐ τ ∂volume.restrict (Ioo ρ R), ∀ᵐ x ∂surfaceMeasure τ, P x := by
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have havoid : ∀ᵐ x ∂volume.restrict (cubicalAnnulus (n + 1) ρ R), x ∉ N := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  have hs := surface_ae_of_annulus_ae hρ hN.compl havoid
  filter_upwards [hs] with τ hτ
  filter_upwards [hτ] with x hx
  by_contra hn
  exact hx (hsub hn)

/-- The centered energy maximal function is unchanged by an ambient a.e.
change of density, including nonmeasurable literal representatives. -/
theorem source_surfaceEnergyMaximal_congr_ae {n : ℕ} {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {g h : Vec (n + 1) → ℝ≥0∞}
    (heq : g =ᵐ[volume.restrict (cubicalAnnulus (n + 1) ρ R)] h) :
    surfaceEnergyMaximal ρ R g = surfaceEnergyMaximal ρ R h := by
  have hs := source_surface_ae_of_annulus_ae hρ heq
  have hi : (fun τ => ∫⁻ x, g x ∂surfaceMeasure τ)
      =ᵐ[volume.restrict (Ioo ρ R)] (fun τ => ∫⁻ x, h x ∂surfaceMeasure τ) :=
    hs.mono (fun _ hτ => lintegral_congr_ae hτ)
  have hmeasure : surfaceEnergyMeasure ρ R g = surfaceEnergyMeasure ρ R h :=
    withDensity_congr_ae hi
  unfold surfaceEnergyMaximal
  rw [hmeasure]

/-- Literal ordered densities order their centered maximal functions. -/
theorem source_surfaceEnergyMaximal_mono_ae {n : ℕ} {ρ R : ℝ} (hρ : 0 ≤ ρ)
    {g h : Vec (n + 1) → ℝ≥0∞}
    (hle : g ≤ᵐ[volume.restrict (cubicalAnnulus (n + 1) ρ R)] h) :
    ∀ τ, surfaceEnergyMaximal ρ R g τ ≤ surfaceEnergyMaximal ρ R h τ := by
  have hs := source_surface_ae_of_annulus_ae hρ hle
  have hi : (fun τ => ∫⁻ x, g x ∂surfaceMeasure τ)
      ≤ᵐ[volume.restrict (Ioo ρ R)] (fun τ => ∫⁻ x, h x ∂surfaceMeasure τ) :=
    hs.mono (fun _ hτ => lintegral_mono_ae hτ)
  have hmeasure : surfaceEnergyMeasure ρ R g ≤ surfaceEnergyMeasure ρ R h :=
    withDensity_mono hi
  intro τ
  unfold surfaceEnergyMaximal centeredMaximal
  apply iSup_mono
  intro ε
  apply iSup_mono
  intro _hε
  gcongr

end
end CoarseDeGiorgi.Selection
