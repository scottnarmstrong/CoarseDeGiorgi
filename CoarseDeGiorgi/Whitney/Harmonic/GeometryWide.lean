module

public import CoarseDeGiorgi.Whitney.Harmonic.Geometry
public import CoarseDeGiorgi.Whitney.ExteriorCells
public import CoarseDeGiorgi.Statements.IsPiecewiseHarmonicExtension
public import CoarseDeGiorgi.Statements.IsTriadicWidth
public import CoarseDeGiorgi.Statements.WhitneyCubesProperties
public import CoarseDeGiorgi.Statements.PointSupDist
public import CoarseDeGiorgi.Whitney.SourceWitnessExterior
public import CoarseDeGiorgi.Whitney.SeedClosedCover

/-! Whitney harmonic extension with the wider width bound. -/

@[expose] public section

open Homogenization MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

noncomputable section

variable {d : ℕ}

open CoarseDeGiorgi.Harnack.Replacement

/-- For `cell ∈ 𝒲_h` the closed parent cube lies in the unit cube. -/
theorem near_closedCube_subset_unit {τ ρ₂ h : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ))) (hd : 1 ≤ d)
    (cell : CoarseDeGiorgi.ExteriorCell d τ)
    (hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h) :
    CoarseDeGiorgi.closedTriadicCube cell.1.1 ⊆ CoarseDeGiorgi.originCube 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hh' : h ≤ (1 - τ) / 100 := by
    refine hwidth.trans ?_
    have hnum : ρ₂ - τ ≤ 1 - τ := by linarith
    calc (ρ₂ - τ) / (100 * (d : ℝ)) ≤ (ρ₂ - τ) / 100 := by
          apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
          nlinarith
      _ ≤ (1 - τ) / 100 := by linarith
  intro x hxc
  obtain ⟨hA, hB, hC⟩ := (CoarseDeGiorgi.whitney_cubes hτ hτ1).2.2.2 cell.1.1 cell.1.2 x hxc
  have hnear' : CoarseDeGiorgi.infSupDist (CoarseDeGiorgi.closedTriadicCube cell.1.1)
      (CoarseDeGiorgi.closedReferenceCube (d := d) τ) < h := hnear
  have hs : CoarseDeGiorgi.pointSupDist x (CoarseDeGiorgi.closedReferenceCube (d := d) τ)
      < (1 - τ) / 2 := by
    linarith
  have hne : (CoarseDeGiorgi.closedReferenceCube (d := d) τ).Nonempty :=
    ⟨0, fun i => by simp; linarith⟩
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ CoarseDeGiorgi.closedReferenceCube (d := d) τ,
      dist x y < (1 - τ) / 2 := by
    have := (csInf_lt_iff (⟨0, by rintro _ ⟨y, _, rfl⟩; exact dist_nonneg⟩) (hne.image _)).1 hs
    obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := this
    exact ⟨y, hy, hlt⟩
  intro i
  have h1 := hy i
  have h2 : |x i - y i| ≤ dist x y := by
    have := dist_le_pi_dist x y i
    rwa [Real.dist_eq] at this
  rw [abs_le] at h1
  have h3 := abs_lt.1 (lt_of_le_of_lt h2 hxy)
  constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]

/-- Cells of `𝒲_h` lie in the unit cube. -/
theorem near_cell_subset_unit {τ ρ₂ h : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂) (_hh : 0 < h)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ))) (hd : 1 ≤ d)
    (cell : CoarseDeGiorgi.ExteriorCell d τ)
    (hnear : cell ∈ CoarseDeGiorgi.whitneySimplicesNear τ h) :
    CoarseDeGiorgi.exteriorCellSet cell ⊆ CoarseDeGiorgi.originCube 1 := fun _ hx =>
  near_closedCube_subset_unit hτ hτ1 hρ₂ hτρ hwidth hd cell hnear (cell_subset_closedCube cell hx)

end
end CoarseDeGiorgi.Whitney.Harmonic.Wide
