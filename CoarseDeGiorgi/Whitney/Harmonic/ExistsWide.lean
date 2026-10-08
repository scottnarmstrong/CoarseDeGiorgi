import CoarseDeGiorgi.Whitney.Harmonic.Exists
import CoarseDeGiorgi.Whitney.Harmonic.GeometryWide
import CoarseDeGiorgi.Whitney.Harmonic.Linear
import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec
import CoarseDeGiorgi.Statements.WhitneyAffineExtensionDef
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Weighted.HarmonicProperties
import CoarseDeGiorgi.Weighted.Lipschitz

/-! Whitney harmonic extension with the wider width bound. -/

open Homogenization MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

noncomputable section

variable {d : ℕ}

open CoarseDeGiorgi.Harnack.Replacement

/-- The a-harmonic replacement on one cell of `𝒲_h`. -/
theorem localReplacement {τ ρ₂ h : ℝ} (hd : 3 ≤ d) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    (a : Homogenization.CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (f : Vec d → ℝ) (cell : CoarseDeGiorgi.ExteriorCell d τ)
    (hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h) :
    ∃ p : (Vec d → ℝ) × (Vec d → Vec d),
      CoarseDeGiorgi.IsWeightedSolution a (CoarseDeGiorgi.exteriorCellSet cell) p.1 p.2 ∧
        CoarseDeGiorgi.MemH1a0 a (CoarseDeGiorgi.exteriorCellSet cell)
          (fun x => p.1 x - CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x)
          (fun x => p.2 x - CoarseDeGiorgi.smoothGrad
            (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x) := by
  have : NeZero d := ⟨by omega⟩
  have hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.exteriorCellSet cell) := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_domain (whitneyCell cell)
  have hne : (CoarseDeGiorgi.exteriorCellSet cell).Nonempty := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_nonempty (whitneyCell cell)
  have hsub := near_cell_subset_unit hτ0 hτ1 hρ₂ hτρ hh hwidth (by omega) cell hnear
  have haV := Whitney.lift_coeff_mono ha hsub
  obtain ⟨K, hK⟩ := affineExtension_lipschitzOn_cell hτ0 hτ1 h f cell
  have hseed := Weighted.memH1a_of_lipschitzOn hV hne haV hK Filter.EventuallyEq.rfl
  obtain ⟨H, GH, hsol, hzero, _⟩ := Weighted.harmonic_replacement hV hne haV hseed
  exact ⟨(H, GH), hsol, hzero⟩

/-- The piecewise harmonic extension exists, for any `f` (no Lipschitz hypothesis needed). -/
theorem piecewiseHarmonicExtension_exists_aux {τ ρ₂ h : ℝ} (hd : 3 ≤ d)
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    (a : Homogenization.CoeffField d)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    (f : Vec d → ℝ) :
    ∃ (H : Vec d → ℝ) (GH : Vec d → Vec d),
      CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH := by
  classical
  have : NeZero d := ⟨by omega⟩
  let Near := {c : CoarseDeGiorgi.ExteriorCell d τ //
    c ∈ CoarseDeGiorgi.whitneySimplicesNear τ h}
  have hlocal (c : Near) := localReplacement hd hτ0 hτ1 hρ₂ hτρ hh hwidth a ha f c.1 c.2
  let localPair : Near → (Vec d → ℝ) × (Vec d → Vec d) := fun c => Classical.choose (hlocal c)
  have localPair_spec (c : Near) := Classical.choose_spec (hlocal c)
  let H : Vec d → ℝ := fun x =>
    if hx : ∃ c : Near, x ∈ CoarseDeGiorgi.exteriorCellSet c.1 then
      (localPair (Classical.choose hx)).1 x else 0
  let GH : Vec d → Vec d := fun x =>
    if hx : ∃ c : Near, x ∈ CoarseDeGiorgi.exteriorCellSet c.1 then
      (localPair (Classical.choose hx)).2 x else 0
  have hpoint (c : Near) (x : Vec d) (hx : x ∈ CoarseDeGiorgi.exteriorCellSet c.1) :
      H x = (localPair c).1 x ∧ GH x = (localPair c).2 x := by
    by_cases hsel : ∃ c' : Near, x ∈ CoarseDeGiorgi.exteriorCellSet c'.1
    · let c' : Near := Classical.choose hsel
      have hmem := Classical.choose_spec hsel
      have hsame : c' = c := by
        by_contra hne
        have hne' : c'.1 ≠ c.1 := fun he => hne (Subtype.ext he)
        exact (exteriorCells_disjoint hτ0 hτ1 c'.1 c.1 hne').le_bot ⟨hmem, hx⟩
      dsimp [H, GH]
      simp only [dite_eq_left hsel]
      change Classical.choose hsel = c at hsame
      rw [hsame]
      exact ⟨rfl, rfl⟩
    · exact False.elim (hsel ⟨c, hx⟩)
  refine ⟨H, GH, ?_⟩
  intro cell
  have hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.exteriorCellSet cell) := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_domain (whitneyCell cell)
  constructor
  · intro hnear
    let c : Near := ⟨cell, hnear⟩
    obtain ⟨hsol, hzero⟩ := localPair_spec c
    have hHae : H =ᵐ[volume.restrict (CoarseDeGiorgi.exteriorCellSet cell)] (localPair c).1 := by
      filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
      exact (hpoint c x hx).1
    have hGHae : GH =ᵐ[volume.restrict (CoarseDeGiorgi.exteriorCellSet cell)] (localPair c).2 := by
      filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
      exact (hpoint c x hx).2
    refine ⟨weightedSolution_congr_ae hsol hHae.symm hGHae.symm, ?_⟩
    refine memH1a0_congr_ae hzero ?_ ?_
    · filter_upwards [hHae] with x hx
      rw [hx]
    · filter_upwards [hHae, hGHae] with x hx hx'
      rw [hx']
  · intro hnear
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    have hnone : ¬ ∃ c : Near, x ∈ CoarseDeGiorgi.exteriorCellSet c.1 := by
      rintro ⟨c, hcx⟩
      have hne : c.1 ≠ cell := fun he => hnear (he ▸ c.2)
      exact (exteriorCells_disjoint hτ0 hτ1 c.1 cell hne).le_bot ⟨hcx, hx⟩
    simp [H, GH, hnone]

end
end CoarseDeGiorgi.Whitney.Harmonic.Wide

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

theorem piecewiseHarmonicExtension_exists_proved :
    ∀ d : ℕ, 3 ≤ d → ∀ a : CoeffField d,
      IsWeightedCoeffOn (originCube 1) a →
      ∀ ρ₁ ρ₂ : ℝ, (hρ₁ : 1 / 2 ≤ ρ₁) → (hρ₁₂ : ρ₁ < ρ₂) → (hρ₂ : ρ₂ ≤ 1) →
        ∀ τ : ℝ, (hJ : τ ∈ selectionInterval ρ₁ ρ₂) →
          let hτ0 : (1 / 2 : ℝ) ≤ τ := by
            have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
            linarith
          let hτ1 : τ < 1 := by
            have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
            linarith
          ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - τ) / (100 * (d : ℝ)) →
            ∀ f : Vec d → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K f (cubeSurface τ)) →
              ∃ (H : Vec d → ℝ) (GH : Vec d → Vec d),
                IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH := by
  intro d hd a ha ρ₁ ρ₂ hρ₁ hρ₁₂ hρ₂ τ hJ hτ0 hτ1 h htri hwidth f _hf
  have h1 : ρ₁ + (ρ₂ - ρ₁) / 4 < τ := hJ.1
  have h2 : τ < ρ₁ + (ρ₂ - ρ₁) / 2 := hJ.2
  exact piecewiseHarmonicExtension_exists_aux hd hτ0 hτ1 hρ₂ (by linarith)
    (triadicWidth_pos htri) hwidth a ha f

end CoarseDeGiorgi.Whitney.Harmonic.Wide
