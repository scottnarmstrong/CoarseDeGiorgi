module

public import CoarseDeGiorgi.Whitney.ExteriorCells
public import CoarseDeGiorgi.Whitney.SeedCellAffine
public import CoarseDeGiorgi.Whitney.LiftSurfaceLayer
public import CoarseDeGiorgi.Selection.CommonRadius
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import CoarseDeGiorgi.Whitney.SourceWitnessCells
public import CoarseDeGiorgi.Whitney.SourceWitnessExterior
public import CoarseDeGiorgi.Statements.ExteriorCell
public import CoarseDeGiorgi.Statements.ExteriorCellSet
public import CoarseDeGiorgi.Statements.WhitneySimplicesNear
public import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize
public import CoarseDeGiorgi.Statements.WhitneyCubesProperties

/-! # Geometry of the exterior Whitney simplices for the exterior integral -/

@[expose] public section

namespace CoarseDeGiorgi.ExteriorIntegral

open Homogenization MeasureTheory Set Whitney
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The seed cell of an exterior cell has the same open set. -/
theorem cell_isOpen {τ : ℝ} (cell : ExteriorCell d τ) : IsOpen (exteriorCellSet cell) := by
  rw [← seedCellSet_eq_statement]
  exact Foundations.Simplex.isOpen_kuhnSimplex _ _ _

theorem cell_measurable {τ : ℝ} (cell : ExteriorCell d τ) :
    MeasurableSet (exteriorCellSet cell) :=
  (cell_isOpen cell).measurableSet

/-- Distinct exterior cells have disjoint simplices. -/
theorem cell_disjoint {τ : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    {c b : ExteriorCell d τ} (hne : c ≠ b) :
    Disjoint (exteriorCellSet c) (exteriorCellSet b) := by
  rw [← seedCellSet_eq_statement, ← seedCellSet_eq_statement]
  by_cases hp : c.1.val = b.1.val
  · apply source_seedCells_same_parent_disjoint (c := whitneySeedCellOfExterior c)
      (b := whitneySeedCellOfExterior b) hp
    intro he
    apply hne
    obtain ⟨⟨c1, c1p⟩, c2, c3⟩ := c
    obtain ⟨⟨b1, b1p⟩, b2, b3⟩ := b
    simp only [whitneySeedCellOfExterior, SeedCell.mk.injEq] at he
    obtain ⟨h1, h2, h3⟩ := he
    subst h1; subst h2; subst h3
    rfl
  · exact Disjoint.mono (source_seedCell_subset_open_parent (whitneySeedCellOfExterior c))
      (source_seedCell_subset_open_parent (whitneySeedCellOfExterior b))
      ((CoarseDeGiorgi.whitney_cubes hτ hτ1).1 _ c.1.property _ b.1.property hp)

/-- Collar of an exterior cell of side `3^{scale-1}`. -/
theorem cell_collar [NeZero d] {τ : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (cell : ExteriorCell d τ) :
    exteriorCellSet cell ⊆ Selection.cubicalAnnulus d τ
      (τ + 54 * (3 : ℝ) ^ (cell.1.val.scale - 1)) := by
  rw [← seedCellSet_eq_statement]
  set c : SeedCell d := whitneySeedCellOfExterior cell with hc
  have hD : c.cube ∈ whitneyCubes τ := cell.1.property
  have hscale : seedCellScale c = (3 : ℝ) ^ (cell.1.val.scale - 1) := rfl
  rw [← hscale]
  have hpos : 0 < (τ + 54 * seedCellScale c) / 2 := by
    have hs : 0 < seedCellScale c := zpow_pos (by norm_num : (0 : ℝ) < 3) _
    linarith only [hτ, hs]
  have hclosed : seedCellSet c ⊆ Metric.closedBall (0 : Vec d)
      ((τ + 54 * seedCellScale c) / 2) := by
    intro x hx
    have hg := (seedWhitney_gap_bounds hτ hτ1 hD (seedCellSet_subset_parent c hx)).2
    rw [seedCellScale_parent] at hg
    change ‖x‖ - τ / 2 ≤ 9 * (3 * seedCellScale c) at hg
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith only [hg]
  have hopen : IsOpen (seedCellSet c) := Foundations.Simplex.isOpen_kuhnSimplex _ _ _
  have hball := hopen.subset_interior_iff.mpr hclosed
  rw [interior_closedBall _ hpos.ne'] at hball
  intro x hx
  have hg := (seedWhitney_gap_bounds hτ hτ1 hD (seedCellSet_subset_parent c hx)).1
  have hs := Foundations.Triadic.scaleFactor_pos c.cube
  refine ⟨?_, ?_⟩
  · change τ / 2 < ‖x‖
    change 2 * cubeScaleFactor c.cube < ‖x‖ - τ / 2 at hg
    linarith only [hg, hs]
  · simpa only [Metric.mem_ball, dist_zero_right] using hball hx

/-- Cells of `W_h` have scale `2 cubeScaleFactor < h`. -/
theorem near_scale_lt {τ h : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    {cell : ExteriorCell d τ} (hn : cell ∈ whitneySimplicesNear τ h) :
    2 * cubeScaleFactor cell.1.val < h := by
  have hD := cell.1.property
  have hx : triadicCenter cell.1.val ∈ closedTriadicCube cell.1.val := by
    intro i
    have : 0 < cubeScaleFactor cell.1.val := Foundations.Triadic.scaleFactor_pos _
    rw [sub_self, abs_zero]
    linarith only [this]
  have := ((CoarseDeGiorgi.whitney_cubes hτ hτ1).2.2.2 _ hD _ hx).1
  exact this.trans hn

/-- Every point of the open exterior lies, almost everywhere, in an open exterior cell. -/
theorem ae_exterior_mem_cell {τ : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1) :
    ∀ᵐ x : Vec d ∂volume, x ∉ closedReferenceCube (d := d) τ →
      ∃ cell : ExteriorCell d τ, x ∈ exteriorCellSet cell := by
  filter_upwards [source_seed_cells_ae_interior (d := d)] with x hx hxn
  obtain ⟨D, hD, hxD⟩ := (CoarseDeGiorgi.whitney_cubes hτ hτ1).2.1 x hxn
  obtain ⟨c, hcD, hcl⟩ := seedParent_closedCell_cover D hxD
  have hcD' : c.cube ∈ whitneyCubes τ := hcD.symm ▸ hD
  let ec : ExteriorCell d τ := ⟨⟨c.cube, hcD'⟩, (c.bins, c.order)⟩
  refine ⟨ec, ?_⟩
  have := seedCellSet_eq_statement ec
  rw [← this]
  exact hx c hcl

/-- A cell of `W_h` (with `h ≤ 1`) lies in some layer `W_h^j`. -/
theorem near_exists_layer {τ h : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1) (hh1 : h ≤ 1)
    {cell : ExteriorCell d τ} (hn : cell ∈ whitneySimplicesNear τ h) :
    ∃ j : ℕ, cell ∈ whitneySimplicesNearSize τ h j := by
  have hlt := near_scale_lt hτ hτ1 hn
  have hs : cell.1.val.scale < 0 := by
    by_contra hcon
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ cell.1.val.scale :=
      one_le_zpow₀ (by norm_num) (not_lt.mp hcon)
    have : cubeScaleFactor cell.1.val = (3 : ℝ) ^ cell.1.val.scale := rfl
    linarith only [hlt, h1, hh1, this]
  refine ⟨(1 - cell.1.val.scale).toNat, hn, ?_⟩
  have : (((1 - cell.1.val.scale).toNat : ℕ) : ℤ) = 1 - cell.1.val.scale :=
    Int.toNat_of_nonneg (by omega)
  omega

/-- Real form of the layer scale. -/
theorem layer_scale {τ h : ℝ} {j : ℕ} {cell : ExteriorCell d τ}
    (hc : cell ∈ whitneySimplicesNearSize τ h j) :
    (3 : ℝ) ^ (cell.1.val.scale - 1) = (3 : ℝ) ^ (-(j : ℝ)) := by
  have he : cell.1.val.scale - 1 = -(j : ℤ) := by
    have := hc.2
    omega
  rw [he, ← Real.rpow_intCast]
  simp

theorem layer_small {τ h : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1) {j : ℕ}
    {cell : ExteriorCell d τ} (hc : cell ∈ whitneySimplicesNearSize τ h j) :
    6 * (3 : ℝ) ^ (-(j : ℝ)) < h := by
  have hlt := near_scale_lt hτ hτ1 hc.1
  have h1 : cubeScaleFactor cell.1.val = 3 * (3 : ℝ) ^ (cell.1.val.scale - 1) := by
    have hp := zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0) (cell.1.val.scale - 1)
    rw [sub_add_cancel] at hp
    change (3 : ℝ) ^ cell.1.val.scale = _
    rw [hp, mul_comm]
  rw [layer_scale hc] at h1
  linarith only [hlt, h1]

theorem layer_collar [NeZero d] {τ h : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1) {j : ℕ}
    {cell : ExteriorCell d τ} (hc : cell ∈ whitneySimplicesNearSize τ h j) :
    exteriorCellSet cell ⊆ Selection.cubicalAnnulus d τ
      (τ + 54 * (3 : ℝ) ^ (-(j : ℝ))) := by
  have := cell_collar hτ hτ1 cell
  rwa [layer_scale hc] at this

end

end CoarseDeGiorgi.ExteriorIntegral
