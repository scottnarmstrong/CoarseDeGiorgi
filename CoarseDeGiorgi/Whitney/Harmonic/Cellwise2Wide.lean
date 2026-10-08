module

public import CoarseDeGiorgi.Whitney.Harmonic.GeometryWide
public import CoarseDeGiorgi.Whitney.Harmonic.Cellwise
public import CoarseDeGiorgi.Statements.WhitneyInterpolationSpec

/-! Range bounds for the piecewise harmonic extension. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

/-- The data of a near cell: affine form of `L_h f`, solution property and zero-boundary class. -/
theorem near_cell_data (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} {f : Vec d → ℝ} {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    (cell : CoarseDeGiorgi.ExteriorCell d τ) (hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h) :
    ∃ (e : Vec d) (c : ℝ),
      (∀ x ∈ CoarseDeGiorgi.exteriorCellSet cell,
        CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x = vecDot e x + c) ∧
      (∀ x ∈ CoarseDeGiorgi.exteriorCellSet cell,
        CoarseDeGiorgi.smoothGrad (CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1) x = e) ∧
      CoarseDeGiorgi.exteriorCellSet cell ⊆ CoarseDeGiorgi.originCube 1 ∧
      IsWeightedSolution a (CoarseDeGiorgi.exteriorCellSet cell) H GH ∧
      MemH1a0 a (CoarseDeGiorgi.exteriorCellSet cell)
        (fun x => H x - CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x)
        (fun x => GH x - e) := by
  obtain ⟨e, c, hec⟩ := ((CoarseDeGiorgi.whitneyInterpolation_spec hτ0 hτ1
    (CoarseDeGiorgi.whitneyFreeValue τ h f)).1).2.2.1 cell
  have hcellOpen : IsOpenBoundedConvexDomain (CoarseDeGiorgi.exteriorCellSet cell) := by
    rw [cellSet_eq_whitney]
    exact Whitney.source_cell_domain (whitneyCell cell)
  have hL : ∀ x ∈ CoarseDeGiorgi.exteriorCellSet cell,
      CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x = vecDot e x + c := hec
  have hG := smoothGrad_eq_of_affine hcellOpen.isOpen e c hL
  obtain ⟨hsol, h0⟩ := (hHGH cell).1 hnear
  refine ⟨e, c, hL, hG, near_cell_subset_unit hτ0 hτ1 hρ₂ hτρ hh hwidth (by omega) cell hnear,
    hsol, ?_⟩
  refine memH1a0_congr_ae h0 EventuallyEq.rfl ?_
  filter_upwards [ae_restrict_mem hcellOpen.isOpen.measurableSet] with x hx
  rw [hG x hx]

variable [NeZero d]

/-- Range bounds for `H_h f`. -/
theorem range_bound (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} (hfacts : AffFacts τ h ρ₂ hτ0 hτ1 f)
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    (m M : ℝ) (hm : m ≤ 0) (hM : 0 ≤ M)
    (hf : ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, m ≤ f y ∧ f y ≤ M) :
    ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ,
      m ≤ H x ∧ H x ≤ M := by
  have hτpos : 0 < τ := by linarith
  have hBc := isClosed_closedRef (d := d) hτpos.le
  refine ae_of_cells hτ0 hτ1 hBc.isOpen_compl.measurableSet subset_rfl (fun cell => ?_)
  by_cases hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h
  · obtain ⟨e, c, hL, _, hUV, hsol, h0⟩ := near_cell_data hd hτ0 hτ1 hρ₂ hτρ hh hwidth hHGH cell hnear
    have hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.exteriorCellSet cell) := by
      rw [cellSet_eq_whitney]
      exact Whitney.source_cell_domain (whitneyCell cell)
    have hne : (CoarseDeGiorgi.exteriorCellSet cell).Nonempty := by
      rw [cellSet_eq_whitney]
      exact Whitney.source_cell_nonempty (whitneyCell cell)
    have hrange := replacement_range hV hne (Whitney.lift_coeff_mono ha hUV) e c m M hL hsol h0
      (fun x hx => hfacts.range m M hm hM hf x
        (fun hxB => (Set.disjoint_left.mp (cell_disjoint_closedRef hτ0 hτ1 cell)) hx hxB))
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hrange
  · have hz := (hHGH cell).2 hnear
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
      (hz.mono fun x hx => by rw [hx.1]; exact ⟨hm, hM⟩)

/-- Nonnegativity of `H_h f`. -/
theorem nonneg_bound (hd : 3 ≤ d) {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ)))
    {a : CoeffField d} (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {f : Vec d → ℝ} (hfacts : AffFacts τ h ρ₂ hτ0 hτ1 f)
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH)
    (hf : ∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, 0 ≤ f y) :
    ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ, 0 ≤ H x := by
  have hτpos : 0 < τ := by linarith
  have hBc := isClosed_closedRef (d := d) hτpos.le
  refine ae_of_cells hτ0 hτ1 hBc.isOpen_compl.measurableSet subset_rfl (fun cell => ?_)
  by_cases hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h
  · obtain ⟨e, c, hL, _, hUV, hsol, h0⟩ := near_cell_data hd hτ0 hτ1 hρ₂ hτρ hh hwidth hHGH cell hnear
    have hV : IsOpenBoundedConvexDomain (CoarseDeGiorgi.exteriorCellSet cell) := by
      rw [cellSet_eq_whitney]
      exact Whitney.source_cell_domain (whitneyCell cell)
    have hne : (CoarseDeGiorgi.exteriorCellSet cell).Nonempty := by
      rw [cellSet_eq_whitney]
      exact Whitney.source_cell_nonempty (whitneyCell cell)
    have hrange := replacement_lower hV hne (Whitney.lift_coeff_mono ha hUV) e c 0 hL hsol h0
      (fun x hx => hfacts.nonneg hf x
        (fun hxB => (Set.disjoint_left.mp (cell_disjoint_closedRef hτ0 hτ1 cell)) hx hxB))
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hrange
  · have hz := (hHGH cell).2 hnear
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
      (hz.mono fun x hx => by rw [hx.1])

end CoarseDeGiorgi.Whitney.Harmonic.Wide
