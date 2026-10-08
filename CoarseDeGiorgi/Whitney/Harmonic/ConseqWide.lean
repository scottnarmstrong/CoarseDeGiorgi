import CoarseDeGiorgi.Whitney.Harmonic.StructWide

/-! The gluing assertion and the `W^{1,1}` assertions of Proposition `p.whitney.extension`. -/

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

open scoped Classical in
/-- The gluing assertion. -/
theorem gluing_statement (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} (hfacts : AffFacts τ h ρ₂ hτ0 hτ1 f)
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    (w : Vec d → ℝ)
    (hw : ∃ K : ℝ≥0, LipschitzOnWith K w (CoarseDeGiorgi.closedReferenceCube (d := d) τ))
    (hwf : ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, w y = f y) :
    ∃ G : Vec d → Vec d,
      MemH1a0 a (CoarseDeGiorgi.originCube (d := d) 1)
        (fun x => if x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ then w x else H x) G ∧
      (∃ K : Set (Vec d), IsCompact K ∧ K ⊆ CoarseDeGiorgi.originCube (d := d) ρ₂ ∧
        ∀ᵐ x ∂volume, x ∉ K →
          (if x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ then w x else H x) = 0) ∧
      ((∀ x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ, 0 ≤ w x) →
        ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.originCube (d := d) 1),
          0 ≤ (if x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ then w x else H x)) := by
  have : NeZero d := ⟨by omega⟩
  have hτpos : 0 < τ := by linarith
  obtain ⟨K₂, hK₂⟩ := hw
  obtain ⟨Φ, K, ξ, Gξ, hΦ, hΦB, hξ, hψ, hH, hB⟩ :=
    glued_correction hd hτ0 hτ1 hρ₂ hτρ hh hwidth ha hfacts hHGH hK₂ hwf
  have hOd : IsOpenBoundedConvexDomain (CoarseDeGiorgi.originCube (d := d) 1) :=
    Whitney.source_cube_domain (by norm_num)
  have hBc := isClosed_closedRef (d := d) hτpos.le
  have hBO := closedRef_subset_unit (d := d) hτ1
  have hae : (fun x => if x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ then w x else H x)
      =ᵐ[volume.restrict (CoarseDeGiorgi.originCube (d := d) 1)] (Φ + ξ) := by
    have hsplit : ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.originCube (d := d) 1),
        x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ ∨
          x ∈ CoarseDeGiorgi.originCube (d := d) 1 \ CoarseDeGiorgi.closedReferenceCube (d := d) τ := by
      filter_upwards [ae_restrict_mem hOd.isOpen.measurableSet] with x hx
      by_cases hxB : x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ
      · exact Or.inl hxB
      · exact Or.inr ⟨hx, hxB⟩
    have hB' : ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.originCube (d := d) 1),
        x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ → ξ x = 0 := by
      have := (ae_restrict_iff' hBc.measurableSet).mp hB
      exact (ae_restrict_of_ae this).mono fun x hx hxB => (hx hxB).1
    have hH' : ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.originCube (d := d) 1),
        x ∈ CoarseDeGiorgi.originCube (d := d) 1 \ CoarseDeGiorgi.closedReferenceCube (d := d) τ →
          H x = Φ x + ξ x := by
      have := (ae_restrict_iff' (hOd.isOpen.measurableSet.diff hBc.measurableSet)).mp
        (hH.mono fun x hx => hx.1)
      exact ae_restrict_of_ae this
    filter_upwards [hsplit, hB', hH'] with x h1 h2 h3
    rcases h1 with hxB | hxS
    · simp only [hxB, ite_true]
      change w x = Φ x + ξ x
      rw [hΦB x hxB, h2 hxB, add_zero]
    · have hxB : x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) τ := hxS.2
      simp only [hxB, ite_false]
      exact h3 hxS
  refine ⟨CoarseDeGiorgi.smoothGrad Φ + Gξ,
    memH1a0_congr_ae hψ hae.symm EventuallyEq.rfl,
    ⟨CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h),
      isCompact_closedRef (by linarith), hfacts.suppO, ?_⟩, ?_⟩
  · have hv := vanishing_outside hτ0 hτ1 hh (a := a) hfacts hHGH
    have hK3 : IsClosed (CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h)) :=
      isClosed_closedRef (by linarith)
    have := (ae_restrict_iff' hK3.isOpen_compl.measurableSet).mp hv
    filter_upwards [this] with x hx hxK
    have hxB : x ∉ CoarseDeGiorgi.closedReferenceCube (d := d) τ := fun hb =>
      hxK (fun i => (hb i).trans (by linarith))
    simp only [hxB, ite_false]
    exact hx hxK
  · intro hw0
    have hfs : ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, 0 ≤ f y := fun y hy => by
      rw [← hwf y hy]; exact hw0 y (surface_subset_closedRef hτpos hy)
    have hnn := nonneg_bound hd hτ0 hτ1 hρ₂ hτρ hh hwidth ha hfacts hHGH hfs
    have := (ae_restrict_iff' hBc.isOpen_compl.measurableSet).mp hnn
    filter_upwards [ae_restrict_of_ae this] with x hx
    by_cases hxB : x ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ
    · simp only [hxB, ite_true]; exact hw0 x hxB
    · simp only [hxB, ite_false]; exact hx hxB

end CoarseDeGiorgi.Whitney.Harmonic.Wide
