import CoarseDeGiorgi.Statements.UpperCellAverage
import CoarseDeGiorgi.Statements.LowerCellAverage
import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
import CoarseDeGiorgi.Statements.SimplexCellNonempty
import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell
import CoarseDeGiorgi.Weighted.UpperSpecNorm
import CoarseDeGiorgi.Weighted.LowerSpecNorm

/-! # Cell estimates for the negative-regularity norm -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Besov

/-- The level-`k` moment of coefficient cell averages used by
the negative-regularity norm. -/
private noncomputable def matrixCellPowerAverage {d : ℕ}
    (b : Vec d → Mat d) (k : ℕ) (r : ℝ) : ℝ :=
  ((triangulation (d := d) k).attach.sum fun η =>
    Real.rpow ‖volumeAverageMat (simplexCell k η) b‖ r) /
      ((triangulation (d := d) k).card : ℝ)

/-- The response moment on a level is bounded by the corresponding average
of the coefficient cell averages. -/
theorem upperCellAverage_le_matrixCellPowerAverage {d : ℕ}
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (k : ℕ) (p : ℝ) (hp : 1 ≤ p) :
    upperCellAverage a ha k p ≤ matrixCellPowerAverage a k p := by
  classical
  unfold CoarseDeGiorgi.upperCellAverage matrixCellPowerAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro η _
  apply Real.rpow_le_rpow (norm_nonneg _) _ (zero_le_one.trans hp)
  exact Weighted.UpperResponseImpl.upperResponse_norm_le
    (simplexCell_isOpenBoundedConvexDomain k η)
    (simplexCell_nonempty k η)
    (weightedCoeffOn_simplexCell k a ha η)

/-- The inverse-response moment on a level is bounded by the corresponding
average of the inverse-coefficient cell averages. -/
theorem lowerCellAverage_le_matrixCellPowerAverage {d : ℕ}
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (k : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    lowerCellAverage a ha k q ≤ matrixCellPowerAverage (fun x => (a x)⁻¹) k q := by
  classical
  unfold CoarseDeGiorgi.lowerCellAverage matrixCellPowerAverage
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro η _
  apply Real.rpow_le_rpow (norm_nonneg _) _ (zero_le_one.trans hq)
  exact Weighted.LowerResponseImpl.lowerResponseInv_norm_le
    (simplexCell_isOpenBoundedConvexDomain k η)
    (simplexCell_nonempty k η)
    (weightedCoeffOn_simplexCell k a ha η)

end CoarseDeGiorgi.Besov
