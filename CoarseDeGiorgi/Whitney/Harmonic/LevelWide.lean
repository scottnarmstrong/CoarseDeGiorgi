module

public import CoarseDeGiorgi.Whitney.Harmonic.GeometryWide
public import CoarseDeGiorgi.Whitney.SourceWitnessResponse
public import CoarseDeGiorgi.Statements.SimplexIndex
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.WhitneySimplicesNearSize

/-! A near cell of size `3^{-j}` is a simplex of the level-`j` triangulation. -/

@[expose] public section

namespace CoarseDeGiorgi.Whitney.Harmonic.Wide

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open CoarseDeGiorgi.Harnack.Replacement

variable {d : ℕ}

theorem cell_eq_simplexCell {τ ρ₂ h : ℝ} (hτ : 1 / 2 ≤ τ) (hτ1 : τ < 1)
    (hρ₂ : ρ₂ ≤ 1) (hτρ : τ < ρ₂)
    (hwidth : h ≤ (ρ₂ - τ) / (100 * (d : ℝ))) (hd : 1 ≤ d) (j : ℕ)
    (cell : CoarseDeGiorgi.ExteriorCell d τ)
    (hcell : cell ∈ CoarseDeGiorgi.whitneySimplicesNearSize τ h j) :
    ∃ η : CoarseDeGiorgi.SimplexIndex d j,
      CoarseDeGiorgi.exteriorCellSet cell = CoarseDeGiorgi.simplexCell j η := by
  obtain ⟨hnear, hs⟩ := hcell
  let c := whitneyCell cell
  have hl : 0 ≤ Whitney.seedCellLevel c := by
    change 0 ≤ 1 - cell.1.val.scale
    rw [hs]; omega
  have hN : Whitney.seedCellNatLevel c = j := by
    unfold Whitney.seedCellNatLevel
    change (1 - cell.1.val.scale).toNat = j
    rw [hs]; omega
  have hcube := near_closedCube_subset_unit hτ hτ1 hρ₂ hτρ hwidth hd cell hnear
  have hn : Whitney.seedScale (Whitney.seedCellNatLevel c) *
      ((3 ^ Whitney.seedCellNatLevel c : ℕ) : ℝ) = 1 := by
    simp only [Whitney.seedScale, zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  have hm : ∀ i, |(Whitney.seedCellMeshIndex c i : ℝ)| <
      ((3 ^ Whitney.seedCellNatLevel c : ℕ) : ℝ) / 2 := by
    intro i
    have hmem := hcube (Whitney.source_seedCellCenter_mem_parent c) i
    have hi : |Whitney.seedCellCenter c i| < 1 / 2 := by
      rw [abs_lt]; constructor <;> linarith [hmem.1, hmem.2]
    rw [Whitney.seedCellCenter_eq_mesh c hl] at hi
    change |Whitney.seedScale (Whitney.seedCellNatLevel c) *
      (Whitney.seedCellMeshIndex c i : ℝ)| < 1 / 2 at hi
    rw [abs_mul, abs_of_pos (Whitney.seedScale_pos _)] at hi
    nlinarith only [hi, hn, Whitney.seedScale_pos (Whitney.seedCellNatLevel c)]
  let η : CoarseDeGiorgi.SimplexIndex d (Whitney.seedCellNatLevel c) :=
    ⟨(Whitney.seedCellMeshIndex c, c.order), Whitney.source_mesh_mem_triangulation _ _ _ hm⟩
  have he : -(Whitney.seedCellNatLevel c : ℤ) = c.cube.scale - 1 := by
    have := Whitney.seedCellNatLevel_cast c hl
    omega
  have hset : CoarseDeGiorgi.simplexCell (Whitney.seedCellNatLevel c) η = Whitney.seedCellSet c := by
    change CoarseDeGiorgi.simplex _ _ _ = _
    rw [Moments.simplex_eq_kuhnSimplex]
    change Foundations.Simplex.kuhnSimplex _ c.order
      (fun i => Whitney.seedScale (Whitney.seedCellNatLevel c) *
        (Whitney.seedCellMeshIndex c i : ℝ)) = _
    rw [← Whitney.seedCellCenter_eq_mesh c hl, he]
    rfl
  have key : ∀ k, k = Whitney.seedCellNatLevel c →
      ∃ η : CoarseDeGiorgi.SimplexIndex d k, CoarseDeGiorgi.simplexCell k η = Whitney.seedCellSet c := by
    rintro k rfl
    exact ⟨η, hset⟩
  obtain ⟨η', hη'⟩ := key j hN.symm
  exact ⟨η', by rw [cellSet_eq_whitney]; exact hη'.symm⟩

end CoarseDeGiorgi.Whitney.Harmonic.Wide
