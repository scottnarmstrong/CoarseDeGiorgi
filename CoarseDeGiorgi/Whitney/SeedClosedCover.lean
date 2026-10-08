import CoarseDeGiorgi.Whitney.SeedCellAffine
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Closed Kuhn cells cover the closed cube -/
namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set
open scoped Topology
noncomputable section
variable {d : ℕ}

/-- The coordinate interval presentation makes closure explicit. -/
theorem seedSimplexCube_eq_pi (n : ℤ) (z : Vec d) :
    Foundations.Simplex.simplexCube n z =
      Set.pi univ (fun i => Ioo (z i - (3 : ℝ) ^ n / 2) (z i + (3 : ℝ) ^ n / 2)) := by
  ext x
  simp only [Foundations.Simplex.simplexCube, mem_ofPred_eq, mem_pi, mem_univ, forall_true_left,
    mem_Ioo]
  constructor <;> intro hx i <;> specialize hx i <;> constructor <;> linarith only [hx.1, hx.2]

theorem seedSimplexCube_closure (n : ℤ) (z : Vec d) :
    closure (Foundations.Simplex.simplexCube n z) =
      {x | ∀ i, -(3 : ℝ) ^ n / 2 ≤ x i - z i ∧ x i - z i ≤ (3 : ℝ) ^ n / 2} := by
  rw [seedSimplexCube_eq_pi, closure_pi_set]
  have hs : 0 < (3 : ℝ) ^ n := zpow_pos (by norm_num) _
  have hi (i : Fin d) : z i - (3 : ℝ) ^ n / 2 ≠ z i + (3 : ℝ) ^ n / 2 := by linarith only [hs]
  simp only [closure_Ioo (hi _)]
  ext x
  simp only [mem_pi, mem_univ, forall_true_left, mem_Icc, mem_ofPred_eq]
  constructor <;> intro hx i <;> specialize hx i <;> constructor <;> linarith only [hx.1, hx.2]

/-- Almost-everywhere coverage of an open set by a closed set gives exact coverage. -/
theorem seedOpen_subset_closed_of_ae {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [Measure.IsOpenPosMeasure μ] {U C : Set X} (hU : IsOpen U) (hC : IsClosed C)
    (hAE : ∀ᵐ x ∂μ, x ∈ U → x ∈ C) : U ⊆ C := by
  have hz : U ∩ Cᶜ =ᵐ[μ] (∅ : Set X) := by
    filter_upwards [hAE] with x hx
    apply propext
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
    exact fun hxu => not_not.mpr (hx hxu)
  have he := (hU.inter hC.isOpen_compl).ae_eq_empty_iff_eq.mp hz
  intro x hx
  by_contra hxc
  have hm : x ∈ U ∩ Cᶜ := ⟨hx, hxc⟩
  rw [he] at hm
  exact hm

/-- Kuhn face points are included by closure, without a generic-position premise. -/
theorem seedClosedKuhn_cover (n : ℤ) (z : Vec d) :
    closure (Foundations.Simplex.simplexCube n z) ⊆
      ⋃ π : Equiv.Perm (Fin d), closure (Foundations.Simplex.kuhnSimplex n π z) := by
  have hC : IsClosed (⋃ π : Equiv.Perm (Fin d), closure (Foundations.Simplex.kuhnSimplex n π z)) :=
    isClosed_iUnion_of_finite (fun _ => isClosed_closure)
  have hU : IsOpen (Foundations.Simplex.simplexCube n z) := by
    rw [seedSimplexCube_eq_pi]
    exact isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  apply hC.closure_subset_iff.mpr
  apply seedOpen_subset_closed_of_ae volume hU hC
  filter_upwards [Foundations.Simplex.iUnion_kuhnSimplex_ae_eq_cube n z] with x hx
  intro hxU
  obtain ⟨π, hπ⟩ := mem_iUnion.mp (hx.mpr hxU)
  exact mem_iUnion.mpr ⟨π, subset_closure hπ⟩

theorem seedParent_isClosed (D : TriadicCube d) : IsClosed (closedTriadicCube D) := by
  have he : closedTriadicCube D = ⋂ i : Fin d,
      {x : Vec d | |x i - triadicCenter D i| ≤ cubeScaleFactor D / 2} := by
    ext x
    simp only [closedTriadicCube, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (((continuous_apply i).sub continuous_const).abs) continuous_const

theorem seedCell_closure_subset_parent (cell : SeedCell d) :
    closure (seedCellSet cell) ⊆ closedTriadicCube cell.cube :=
  (seedParent_isClosed cell.cube).closure_subset_iff.mpr (seedCellSet_subset_parent cell)

/-- The three closed child intervals cover a closed parent interval, including endpoints. -/
theorem seedFineCube_closure_cover (n : ℤ) (z : Vec d) {x : Vec d}
    (hx : ∀ i, -(3 : ℝ) ^ n / 2 ≤ x i - z i ∧ x i - z i ≤ (3 : ℝ) ^ n / 2) :
    ∃ bins : Fin d → Fin 3, x ∈ closure (Foundations.Simplex.simplexCube (n - 1)
      (Foundations.Simplex.fineCubeCenter n z bins)) := by
  classical
  let s : ℝ := (3 : ℝ) ^ (n - 1)
  let bins : Fin d → Fin 3 := fun i => if x i - z i ≤ -s / 2 then 0 else if x i - z i ≤ s / 2 then 1 else 2
  refine ⟨bins, ?_⟩
  rw [seedSimplexCube_closure]
  intro i
  have hs : 0 < s := zpow_pos (by norm_num) _
  have hscale : (3 : ℝ) ^ n = 3 * s := by
    dsimp [s]
    rw [zpow_sub_one₀ (by norm_num)]
    field_simp
  have hi := hx i
  rw [hscale] at hi
  change -s / 2 ≤ x i - (z i + s * ((bins i).val - 1 : ℝ)) ∧
    x i - (z i + s * ((bins i).val - 1 : ℝ)) ≤ s / 2
  dsimp [bins]
  split_ifs with hlow hhigh <;> norm_num <;> constructor <;> linarith

/-- Every point of a selected parent's closure lies in a closed child Kuhn cell. -/
theorem seedParent_closedCell_cover (D : TriadicCube d) {x : Vec d} (hx : x ∈ closedTriadicCube D) :
    ∃ cell : SeedCell d, cell.cube = D ∧ x ∈ closure (seedCellSet cell) := by
  have hcoord : ∀ i, -(3 : ℝ) ^ D.scale / 2 ≤ x i - triadicCenter D i ∧
      x i - triadicCenter D i ≤ (3 : ℝ) ^ D.scale / 2 := by
    intro i
    simpa only [cubeScaleFactor, neg_div] using abs_le.mp (hx i)
  obtain ⟨bins, hbins⟩ := seedFineCube_closure_cover D.scale (triadicCenter D) hcoord
  obtain ⟨π, hπ⟩ := mem_iUnion.mp (seedClosedKuhn_cover _ _ hbins)
  exact ⟨⟨D, bins, π⟩, rfl, hπ⟩

end
end CoarseDeGiorgi.Whitney

