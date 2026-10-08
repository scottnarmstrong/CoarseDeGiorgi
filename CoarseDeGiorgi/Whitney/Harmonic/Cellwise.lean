module

public import CoarseDeGiorgi.Whitney.Harmonic.Admissible
public import CoarseDeGiorgi.Whitney.Harmonic.Range
public import CoarseDeGiorgi.Statements.EuclidLipConst

/-! Cellwise consequences of `IsPiecewiseHarmonicExtension`: vanishing and range bounds. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

/-- Almost everywhere statements on a set `S` outside the reference cube may be checked cell by cell. -/
theorem ae_of_cells {τ : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) {S : Set (Vec d)}
    (hS : MeasurableSet S) (hSB : S ⊆ (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ)
    {P : Vec d → Prop}
    (h : ∀ cell : CoarseDeGiorgi.ExteriorCell d τ,
      ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.exteriorCellSet cell ∩ S), P x) :
    ∀ᵐ x ∂volume.restrict S, P x := by
  have hcm (cell : CoarseDeGiorgi.ExteriorCell d τ) :
      MeasurableSet (CoarseDeGiorgi.exteriorCellSet cell) := by
    rw [cellSet_eq_whitney]
    exact (Whitney.source_cell_domain (whitneyCell cell)).isOpen.measurableSet
  have hU := (ae_restrict_iUnion_iff (μ := volume.restrict S)
    (fun cell : CoarseDeGiorgi.ExteriorCell d τ => CoarseDeGiorgi.exteriorCellSet cell) P).mpr
    (fun cell => by
      rw [Measure.restrict_restrict (hcm cell)]
      exact h cell)
  rw [ae_restrict_iff' (MeasurableSet.iUnion hcm)] at hU
  have hcover := ae_exists_cell (d := d) hτ0 hτ1
  filter_upwards [ae_restrict_of_ae hcover, ae_restrict_mem hS, hU] with x h1 h2 h3
  obtain ⟨cell, hcell⟩ := h1 (hSB h2)
  exact h3 (mem_iUnion.mpr ⟨cell, hcell⟩)

/-- The hypotheses of Proposition `p.affine.extension` for a fixed boundary datum `f`, used by the
proof. -/
structure AffFacts (τ h ρ₂ : ℝ) (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) (f : Vec d → ℝ) : Prop where
  nonneg : (∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, 0 ≤ f y) →
    ∀ x ∈ (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ,
      0 ≤ CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x
  lipF : ∃ F : Vec d → ℝ,
    (∀ x ∈ (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ,
      F x = CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x) ∧
    (∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, F y = f y) ∧
    CoarseDeGiorgi.euclidLipConst (CoarseDeGiorgi.originCube (d := d) τ)ᶜ F < ⊤
  range : ∀ m M : ℝ, m ≤ 0 → 0 ≤ M →
    (∀ y ∈ CoarseDeGiorgi.cubeSurface (d := d) τ, m ≤ f y ∧ f y ≤ M) →
    ∀ x ∈ (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ,
      m ≤ CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x ∧
        CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x ≤ M
  zero : ∀ cell : CoarseDeGiorgi.ExteriorCell d τ, cell ∉ CoarseDeGiorgi.whitneySimplicesNear τ h →
    ∀ x ∈ CoarseDeGiorgi.exteriorCellSet cell,
      CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x = 0
  cellsupp : ∀ cell : CoarseDeGiorgi.ExteriorCell d τ, cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h →
    closure (CoarseDeGiorgi.exteriorCellSet cell) ⊆
      CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h)
  supp : closure {x | x ∈ (CoarseDeGiorgi.closedReferenceCube (d := d) τ)ᶜ ∧
      CoarseDeGiorgi.whitneyAffineExtension τ h f hτ0 hτ1 x ≠ 0} ⊆
    CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h)
  suppO : CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h) ⊆
    CoarseDeGiorgi.originCube (d := d) ρ₂

/-- `H_h f` vanishes outside `(τ+3h)□̄₀`. -/
theorem vanishing_outside {τ ρ₂ h : ℝ} (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (hh : 0 < h) {a : CoeffField d} {f : Vec d → ℝ} (hfacts : AffFacts τ h ρ₂ hτ0 hτ1 f)
    {H : Vec d → ℝ} {GH : Vec d → Vec d}
    (hHGH : CoarseDeGiorgi.IsPiecewiseHarmonicExtension a τ h hτ0 hτ1 f H GH) :
    ∀ᵐ x ∂volume.restrict (CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h))ᶜ, H x = 0 := by
  have hτpos : 0 < τ := by linarith
  have hK3 : IsClosed (CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h)) :=
    isClosed_closedRef (by linarith)
  have hBK : CoarseDeGiorgi.closedReferenceCube (d := d) τ ⊆
      CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h) := by
    intro x hx i
    exact (hx i).trans (by linarith)
  refine ae_of_cells hτ0 hτ1 hK3.isOpen_compl.measurableSet
    (Set.compl_subset_compl.mpr hBK) (fun cell => ?_)
  by_cases hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h
  · have hempty : CoarseDeGiorgi.exteriorCellSet cell ∩
        (CoarseDeGiorgi.closedReferenceCube (d := d) (τ + 3 * h))ᶜ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨hx, hxK⟩
      exact hxK (hfacts.cellsupp cell hnear (subset_closure hx))
    rw [hempty, Measure.restrict_empty]
    simp
  · have hz := ((hHGH cell).2 hnear)
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left
      (hz.mono fun x hx => hx.1)

end CoarseDeGiorgi.Whitney.Harmonic
