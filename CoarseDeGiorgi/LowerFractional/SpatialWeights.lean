import CoarseDeGiorgi.LowerFractional.MomentSeries
import CoarseDeGiorgi.Foundations.Simplex.Partition

/-! Actual spatial weights of the triangulation (`l.lower.averages`).
This identifies volume-weighted simplex response powers with the cell average
used in lowerMoment, rather than introducing an unrelated sequence of weights. -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- Every simplex in the level-k triangulation has reciprocal-cardinality volume. -/
theorem simplexCell_volume_toReal {d : ℕ} (k : ℕ)
    (η : {v : (Fin d → ℤ) × Equiv.Perm (Fin d) // v ∈ triangulation k}) :
    (volume (simplexCell k (show CoarseDeGiorgi.SimplexIndex d k from η))).toReal =
      ((triangulation (d := d) k).card : ℝ)⁻¹ := by
  let η' : SimplexIndex d k := show SimplexIndex d k from η
  have hcell : simplexCell k η' = Foundations.Simplex.kuhnSimplex (-(k : ℤ)) η'.1.2
      (fun i => (3 : ℝ) ^ (-(k : ℤ)) * (η'.1.1 i : ℝ)) :=
    Moments.simplex_eq_kuhnSimplex _ _ _
  rw [hcell, Foundations.Simplex.volume_kuhnSimplex, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (zpow_pos (by norm_num) _).le, ENNReal.toReal_natCast,
    triangulation_card]
  push_cast
  rw [show -(k : ℤ) * (d : ℤ) = -((k * d : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast]
  simp only [div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- The actual volume-weighted sum is the audited arithmetic cell average. -/
theorem lower_spatial_weight_eq_cellAverage {d : ℕ} (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (q : ℝ) :
    ((triangulation (d := d) k).attach.sum fun η =>
      (volume (simplexCell k η)).toReal * ‖lowerResponseInvOnCell k a ha η‖ ^ q) =
      lowerCellAverage a ha k q := by
  classical
  change ((triangulation (d := d) k).attach.sum fun η : CoarseDeGiorgi.SimplexIndex d k =>
    (volume (simplexCell k η)).toReal * ‖lowerResponseInvOnCell k a ha η‖ ^ q) = _
  unfold CoarseDeGiorgi.lowerCellAverage
  unfold CoarseDeGiorgi.SimplexIndex at ⊢
  simp_rw [simplexCell_volume_toReal, mul_comm (((triangulation (d := d) k).card : ℝ)⁻¹)]
  rw [← Finset.sum_mul, div_eq_mul_inv]
  rfl

/-- Restricting the actual spatial weight to any subcollection only decreases it. -/
theorem lower_spatial_weight_subcollection_le {d : ℕ} (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (q : ℝ)
    (s : Finset (SimplexIndex d k)) :
    (∑ η ∈ s, (volume (simplexCell k η)).toReal *
      ‖lowerResponseInvOnCell k a ha η‖ ^ q) ≤ lowerCellAverage a ha k q := by
  classical
  rw [← lower_spatial_weight_eq_cellAverage]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro η _
    exact Finset.mem_attach _ _
  · intro η _ _
    exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _)



end CoarseDeGiorgi.LowerFractional
