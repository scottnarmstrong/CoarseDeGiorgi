import CoarseDeGiorgi.Whitney.Harmonic.Cellwise2Wide

/-! Linearity of the piecewise harmonic extension in the datum. -/

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ} [NeZero d]

theorem linearity_ae (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f₁ f₂ : Vec d → ℝ} (c₁ c₂ : ℝ)
    (hlin : ∀ x ∈ (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ,
      CoarseDeGiorgi.whitneyAffineExtension τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) hτ0 hτ1 x =
        c₁ * CoarseDeGiorgi.whitneyAffineExtension τ h f₁ hτ0 hτ1 x +
          c₂ * CoarseDeGiorgi.whitneyAffineExtension τ h f₂ hτ0 hτ1 x)
    {H₁ H₂ H : Vec d → ℝ} {GH₁ GH₂ GH : Vec d → Vec d}
    (h₁ : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f₁ H₁ GH₁)
    (h₂ : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f₂ H₂ GH₂)
    (h₀ : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1
      (fun y => c₁ * f₁ y + c₂ * f₂ y) H GH) :
    ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ,
      H x = c₁ * H₁ x + c₂ * H₂ x ∧ GH x = c₁ • GH₁ x + c₂ • GH₂ x := by
  have hτpos : 0 < τ := by linarith
  have hBc := isClosed_closedRef (d := d) hτpos.le
  refine ae_of_cells hτ0 hτ1 hBc.isOpen_compl.measurableSet subset_rfl (fun cell => ?_)
  by_cases hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h
  · obtain ⟨e, c, hL, hG, hUV, hsol, h0⟩ :=
      near_cell_data hd hτ0 hτ1 hρ₂ hτρ hh hwidth h₀ cell hnear
    obtain ⟨e₁, c₁', hL₁, hG₁, -, hsol₁, h01⟩ :=
      near_cell_data hd hτ0 hτ1 hρ₂ hτρ hh hwidth h₁ cell hnear
    obtain ⟨e₂, c₂', hL₂, hG₂, -, hsol₂, h02⟩ :=
      near_cell_data hd hτ0 hτ1 hρ₂ hτρ hh hwidth h₂ cell hnear
    have hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.exteriorCellSet cell) := by
      rw [cellSet_eq_whitney]
      exact Whitney.source_cell_domain (whitneyCell cell)
    have hne : (CoarseDeGiorgi.exteriorCellSet cell).Nonempty := by
      rw [cellSet_eq_whitney]
      exact Whitney.source_cell_nonempty (whitneyCell cell)
    have hLc : ∀ x ∈ CoarseDeGiorgi.exteriorCellSet cell,
        CoarseDeGiorgi.whitneyAffineExtension τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) hτ0 hτ1 x =
          c₁ * CoarseDeGiorgi.whitneyAffineExtension τ h f₁ hτ0 hτ1 x +
            c₂ * CoarseDeGiorgi.whitneyAffineExtension τ h f₂ hτ0 hτ1 x :=
      fun x hx => hlin x
        (fun hxB => (Set.disjoint_left.mp (cell_disjoint_closedRef hτ0 hτ1 cell)) hx hxB)
    have hegrad : e = c₁ • e₁ + c₂ • e₂ := by
      obtain ⟨x0, hx0⟩ := hne
      have hcomb := smoothGrad_eq_of_affine hV.isOpen (c₁ • e₁ + c₂ • e₂) (c₁ * c₁' + c₂ * c₂')
        (Φ := CoarseDeGiorgi.whitneyAffineExtension τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) hτ0 hτ1)
        (fun x hx => by
          rw [hLc x hx, hL₁ x hx, hL₂ x hx]
          simp only [vecDot_add_left, vecDot_smul_left]
          ring) x0 hx0
      rw [← hcomb, ← hG x0 hx0]
    have hrep := replacement_linear hV hne (Whitney.lift_coeff_mono ha hUV) c₁ c₂
      (L := CoarseDeGiorgi.whitneyAffineExtension τ h (fun y => c₁ * f₁ y + c₂ * f₂ y) hτ0 hτ1)
      (L₁ := CoarseDeGiorgi.whitneyAffineExtension τ h f₁ hτ0 hτ1)
      (L₂ := CoarseDeGiorgi.whitneyAffineExtension τ h f₂ hτ0 hτ1)
      (G := fun _ => e) (G₁ := fun _ => e₁) (G₂ := fun _ => e₂)
      (Filter.eventually_of_mem (ae_restrict_mem hV.isOpen.measurableSet) hLc)
      (Filter.Eventually.of_forall fun x => by simp [hegrad])
      hsol hsol₁ hsol₂ h0 h01 h02
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
      (hrep.1.and hrep.2)
  · have z0 := (h₀ cell).2 hnear
    have z1 := (h₁ cell).2 hnear
    have z2 := (h₂ cell).2 hnear
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
      (by
        filter_upwards [z0, z1, z2] with x a0 a1 a2
        rw [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2]
        simp)

end CoarseDeGiorgi.Whitney.Harmonic.Wide
