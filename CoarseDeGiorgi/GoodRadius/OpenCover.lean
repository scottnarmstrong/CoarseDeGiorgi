module

public import CoarseDeGiorgi.Selection.SourceRepresentatives

/-!
# Equality near every surface gives equality on almost every surface

If for every radius in a set `J` there is an open neighborhood of the surface on which two
functions agree almost everywhere, then they agree `surfaceMeasure τ`-a.e. for almost every
`τ ∈ J` (Lindelöf plus the cubical coarea formula).
-/

@[expose] public section

namespace CoarseDeGiorgi.GoodRadius

open Homogenization MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

theorem surface_ae_eq_of_local_cover {n : ℕ} {ρ R : ℝ} (hρ : 0 ≤ ρ) {J : Set ℝ}
    (hJm : MeasurableSet J) (hJ : J ⊆ Ioo ρ R) {F w : Vec (n + 1) → ℝ}
    (hcov : ∀ τ ∈ J, ∃ U : Set (Vec (n + 1)), IsOpen U ∧ cubeSurface τ ⊆ U ∧
      ∀ᵐ x ∂(volume.restrict U), F x = w x) :
    ∀ᵐ τ ∂(volume.restrict J), F =ᵐ[surfaceMeasure τ] w := by
  choose! U hUo hUs hUae using hcov
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun τ : J => U τ) (fun τ => hUo τ τ.2)
  let Us : Set (Vec (n + 1)) := ⋃ τ : J, U τ
  have hUsO : IsOpen Us := isOpen_iUnion fun τ => hUo τ τ.2
  have hae : ∀ᵐ x ∂(volume.restrict Us), F x = w x := by
    change ∀ᵐ x ∂(volume.restrict (⋃ τ : J, U τ)), F x = w x
    rw [← hT, ae_restrict_biUnion_iff (fun τ : J => U τ) hTc]
    intro τ _
    exact hUae τ τ.2
  have hae' : ∀ᵐ x ∂(volume : Measure (Vec (n + 1))), x ∈ Us → F x = w x := by
    rw [← ae_restrict_iff' hUsO.measurableSet]
    exact hae
  have hann : ∀ᵐ x ∂(volume.restrict (CoarseDeGiorgi.Selection.cubicalAnnulus (n + 1) ρ R)), x ∈ Us → F x = w x :=
    ae_restrict_of_ae hae'
  have hs := CoarseDeGiorgi.Selection.source_surface_ae_of_annulus_ae hρ hann
  have hs' := ae_restrict_of_ae_restrict_of_subset hJ hs
  filter_upwards [hs', ae_restrict_mem hJm] with τ hτ hτJ
  have hτ0 : 0 ≤ τ := hρ.trans (hJ hτJ).1.le
  filter_upwards [hτ, Foundations.FracGeometry.surfaceMeasure_ae_surface (d := n + 1) hτ0]
    with x hx hxs
  exact hx (mem_iUnion.mpr ⟨⟨τ, hτJ⟩, hUs τ hτJ hxs⟩)

end

end CoarseDeGiorgi.GoodRadius
