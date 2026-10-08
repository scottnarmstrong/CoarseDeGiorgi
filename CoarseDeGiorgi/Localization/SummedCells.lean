module

public import CoarseDeGiorgi.Localization.Geometry
public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import CoarseDeGiorgi.Statements.LowerCellAverage
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Statements.TriangulationIn
public import CoarseDeGiorgi.Statements.SimplexCellNonempty
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn

/-! # Cells of the level-`k` triangulation counted over a bounded-overlap cover

For a family of auxiliary cubes with overlap at most `4^d`, the sum over the cubes of the
weights of the cells contained in each cube is at most `4^d` times the weight of the whole
triangulation, which is `ofReal (lowerCellAverage ..)`. -/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

/-- All cells of level `k`, as a finset of `SimplexIndex d k`. -/
def allCells (d k : ℕ) : Finset (SimplexIndex d k) := (triangulation (d := d) k).attach

theorem mem_allCells {k : ℕ} (η : SimplexIndex d k) : η ∈ allCells d k :=
  Finset.mem_attach _ _

theorem mem_triangulationIn_iff {k : ℕ} {U : Set (Vec d)} {η : SimplexIndex d k} :
    η ∈ triangulationIn (d := d) k U ↔ simplexCell k η ⊆ U := by
  unfold triangulationIn
  exact Iff.trans (Finset.mem_filter (s := allCells d k)) ⟨fun h => h.2, fun h => ⟨mem_allCells η, h⟩⟩

/-- The weight of all cells of level `k` is `ofReal` of the lower cell average. -/
theorem sum_cells_weight_eq (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (k : ℕ) (q : ℝ) :
    (∑ η ∈ allCells d k, volume (simplexCell k η) *
        ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)) =
      ENNReal.ofReal (lowerCellAverage a ha k q) := by
  have hN : (0 : ℝ) < ((triangulation (d := d) k).card : ℝ) := by
    rw [triangulation_card]; positivity
  have hvol : ∀ η : SimplexIndex d k, volume (simplexCell k η) =
      ENNReal.ofReal (((triangulation (d := d) k).card : ℝ)⁻¹) := by
    intro η
    rw [← CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.simplexCell_volume_real k η,
      ENNReal.ofReal_toReal]
    exact (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
  have hnn : ∀ η : SimplexIndex d k, 0 ≤ Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q :=
    fun η => Real.rpow_nonneg (norm_nonneg _) _
  have hdef : lowerCellAverage a ha k q = (∑ η ∈ allCells d k,
      Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q) / ((triangulation (d := d) k).card : ℝ) := rfl
  rw [hdef, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hN.le),
    ENNReal.ofReal_sum_of_nonneg (fun η _ => hnn η), Finset.mul_sum]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [hvol]

/-- Overlap count of cells: each cell lies in at most `4^d` cubes of the family. -/
theorem sum_cells_overlap_le (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (m : ℤ) (Z : Finset (Fin d → ℤ)) (k : ℕ) (q : ℝ) :
    (∑ z ∈ Z, ∑ η ∈ triangulationIn (d := d) k (auxCube m z), volume (simplexCell k η) *
        ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)) ≤
      ((4 ^ d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (lowerCellAverage a ha k q) := by
  rw [← sum_cells_weight_eq, Finset.mul_sum]
  set g : SimplexIndex d k → ℝ≥0∞ := fun η => volume (simplexCell k η) *
        ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q) with hg
  have hswap : (∑ z ∈ Z, ∑ η ∈ triangulationIn (d := d) k (auxCube m z), g η) =
      ∑ η ∈ allCells d k,
        ((Z.filter fun z => η ∈ triangulationIn (d := d) k (auxCube m z)).card : ℝ≥0∞) * g η := by
    have h1 : ∀ z ∈ Z, (∑ η ∈ triangulationIn (d := d) k (auxCube m z), g η) =
        ∑ η ∈ allCells d k, if η ∈ triangulationIn (d := d) k (auxCube m z) then g η else 0 := by
      intro z _
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (fun η _ => mem_allCells η)]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  refine Finset.sum_le_sum fun η _ => ?_
  refine mul_le_mul_left ?_ _
  obtain ⟨x, hx⟩ := simplexCell_nonempty k η
  have hcard : (Z.filter fun z => η ∈ triangulationIn (d := d) k (auxCube m z)).card ≤ 4 ^ d := by
    refine le_trans (Finset.card_le_card ?_) (card_filter_closedAuxCube_le m Z x)
    intro z hz
    obtain ⟨hzZ, hη⟩ := Finset.mem_filter.mp hz
    have hsub : simplexCell k η ⊆ auxCube m z := by
      exact mem_triangulationIn_iff.mp hη
    exact Finset.mem_filter.mpr ⟨hzZ, auxCube_subset_closedAuxCube m z (hsub hx)⟩
  exact_mod_cast hcard

end
end CoarseDeGiorgi.Localization
