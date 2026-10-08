import CoarseDeGiorgi.SharpnessExamples.CylinderResponseAverages
import CoarseDeGiorgi.SharpnessExamples.CylinderFractionBridge
import CoarseDeGiorgi.SharpnessExamples.CylinderFiniteMeans
import CoarseDeGiorgi.Besov.CellBounds

/-! # Level bounds for the anisotropic cylinder from coefficient averages

The proof of Proposition `p.sharpness.polynomial` bounds the response means by averages of the
coefficient over the simplices (the bounds `e.upper.norm.bound`, `e.lower.norm.bound`) and the
averages of the diagonal field by the cylinder fractions. No cell response is computed.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The average of the cylinder field over a set has norm at most `1 + A f`. -/
theorem optimalPowers_avg_norm_upper {d : ℕ} [NeZero d] {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) (epsilon : ℝ) {A b : ℝ}
    (hA : 1 ≤ A) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ‖volumeAverageMat V (cylinderCoefficient epsilon A b)‖ ≤
      1 + A * cylinderResponseFraction V epsilon := by
  classical
  obtain ⟨hf0, hf1⟩ := cylinderResponseFraction_bounds hV epsilon
  set f := cylinderResponseFraction V epsilon
  rw [cylinderCoefficient_average hV hvol]
  have hM : 0 ≤ 1 + (A - 1) * f := by nlinarith
  have hn := cylinderDiagonal_norm (d := d) (⟨0, Nat.pos_of_neZero d⟩ : Fin d)
    (parallel := 1 + (A - 1) * f) (perpendicular := 1 + (b - 1) * f)
    (M := 1 + (A - 1) * f) hM
    (by rw [abs_of_nonneg hM]) (by
      rw [abs_le]; constructor <;> nlinarith) (by simp)
  rw [hn]
  nlinarith

/-- The average of the inverse cylinder field over a set has norm at most `1 + b⁻¹ f`. -/
theorem optimalPowers_avg_norm_lower {d : ℕ} (hd : 2 ≤ d) {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) (hvol : (volume V).toReal ≠ 0) (epsilon : ℝ) {A b : ℝ}
    (hA : 1 ≤ A) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    ‖volumeAverageMat V (fun x => (cylinderCoefficient epsilon A b x)⁻¹)‖ ≤
      1 + b⁻¹ * cylinderResponseFraction V epsilon := by
  classical
  obtain ⟨hf0, hf1⟩ := cylinderResponseFraction_bounds hV epsilon
  set f := cylinderResponseFraction V epsilon
  have hA0 : 0 < A := by linarith
  rw [cylinderCoefficient_inverse_average hV hvol epsilon hA0.ne' hb0.ne']
  have hbi : 1 ≤ b⁻¹ := one_le_inv₀ hb0 |>.2 hb1
  have hAi : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  have hAi0 : 0 < A⁻¹ := inv_pos.2 hA0
  have hM : 0 ≤ 1 + (b⁻¹ - 1) * f := by nlinarith
  have hn := cylinderDiagonal_norm (d := d) (⟨1, by omega⟩ : Fin d)
    (parallel := 1 + (A⁻¹ - 1) * f) (perpendicular := 1 + (b⁻¹ - 1) * f)
    (M := 1 + (b⁻¹ - 1) * f) hM
    (by rw [abs_le]; constructor <;> nlinarith) (by rw [abs_of_nonneg hM]) (by simp)
  rw [hn]
  nlinarith

private theorem simplexIndex_nonempty' (d k : ℕ) : Nonempty (SimplexIndex d k) :=
  Fintype.card_pos_iff.mp (by
    simpa [SimplexIndex] using Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)

theorem optimalPowers_finitePowerMean_le {d k : ℕ} {v c : ℝ} (hv : 1 ≤ v) (hc : 0 ≤ c)
    (x f : SimplexIndex d k → ℝ) (hx : ∀ η, 0 ≤ x η) (hf : ∀ η, 0 ≤ f η)
    (hxf : ∀ η, x η ≤ 1 + c * f η) :
    finitePowerMean x v ≤ 1 + c * finitePowerMean f v := by
  let := simplexIndex_nonempty' d k
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  refine le_trans (finitePowerMean_mono hx hxf hv0) ?_
  have h := finitePowerMean_add_le (fun _ : SimplexIndex d k => (1 : ℝ))
    (fun η => c * f η) (by simp) (fun η => mul_nonneg hc (hf η)) hv
  rwa [finitePowerMean_const (by norm_num) hv0, finitePowerMean_smul f hf hc hv0] at h

/-- The upper-response level mean is controlled by the cylinder fractions. -/
theorem optimalPowers_upper_level {d : ℕ} [NeZero d] (k : ℕ) (epsilon : ℝ) {A b v : ℝ}
    (hA : 1 ≤ A) (hb0 : 0 < b) (hb1 : b ≤ 1) (hv : 1 ≤ v)
    (ha : IsWeightedCoeffOn (originCube 1) (cylinderCoefficient (d := d) epsilon A b)) :
    Real.rpow (upperCellAverage (cylinderCoefficient epsilon A b) ha k v) (1 / v) ≤
      1 + A * finitePowerMean
        (fun η : SimplexIndex d k => cylinderResponseFraction (simplexCell k η) epsilon) v := by
  classical
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hfin (η : SimplexIndex d k) : volume (simplexCell k η) ≠ ⊤ :=
    (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
  have hvol (η : SimplexIndex d k) : (volume (simplexCell k η)).toReal ≠ 0 :=
    (ENNReal.toReal_pos ((simplexCell_isOpenBoundedConvexDomain k η).isOpen.measure_pos volume
      (simplexCell_nonempty k η)).ne' (hfin η)).ne'
  have h1 := Besov.upperCellAverage_le_matrixCellPowerAverage
    (cylinderCoefficient epsilon A b) ha k v hv
  have h2 : upperCellAverage (cylinderCoefficient epsilon A b) ha k v ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η) (cylinderCoefficient epsilon A b)‖ v) /
      ((triangulation (d := d) k).card : ℝ) := h1
  have h0 : 0 ≤ upperCellAverage (cylinderCoefficient epsilon A b) ha k v :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _)
  refine le_trans (Real.rpow_le_rpow h0 h2 (by positivity)) ?_
  have hfm : Real.rpow (((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η) (cylinderCoefficient epsilon A b)‖ v) /
      ((triangulation (d := d) k).card : ℝ)) (1 / v) =
      finitePowerMean (fun η : SimplexIndex d k =>
        ‖volumeAverageMat (simplexCell k η) (cylinderCoefficient epsilon A b)‖) v := by
    simp [finitePowerMean, SimplexIndex]
  refine le_trans (le_of_eq hfm) ?_
  exact optimalPowers_finitePowerMean_le hv (by linarith) _ _ (fun _ => norm_nonneg _)
    (fun η => (cylinderResponseFraction_bounds (hfin η) epsilon).1)
    (fun η => optimalPowers_avg_norm_upper (hfin η) (hvol η) epsilon hA hb0 hb1)

/-- The lower-response level mean is controlled by the cylinder fractions. -/
theorem optimalPowers_lower_level {d : ℕ} (hd : 2 ≤ d) (k : ℕ) (epsilon : ℝ) {A b v : ℝ}
    (hA : 1 ≤ A) (hb0 : 0 < b) (hb1 : b ≤ 1) (hv : 1 ≤ v)
    (ha : IsWeightedCoeffOn (originCube 1) (cylinderCoefficient (d := d) epsilon A b)) :
    Real.rpow (lowerCellAverage (cylinderCoefficient epsilon A b) ha k v) (1 / v) ≤
      1 + b⁻¹ * finitePowerMean
        (fun η : SimplexIndex d k => cylinderResponseFraction (simplexCell k η) epsilon) v := by
  classical
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hfin (η : SimplexIndex d k) : volume (simplexCell k η) ≠ ⊤ :=
    (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
  have hvol (η : SimplexIndex d k) : (volume (simplexCell k η)).toReal ≠ 0 :=
    (ENNReal.toReal_pos ((simplexCell_isOpenBoundedConvexDomain k η).isOpen.measure_pos volume
      (simplexCell_nonempty k η)).ne' (hfin η)).ne'
  have h1 := Besov.lowerCellAverage_le_matrixCellPowerAverage
    (cylinderCoefficient epsilon A b) ha k v hv
  have h2 : lowerCellAverage (cylinderCoefficient epsilon A b) ha k v ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η)
          (fun x => (cylinderCoefficient epsilon A b x)⁻¹)‖ v) /
      ((triangulation (d := d) k).card : ℝ) := h1
  have h0 : 0 ≤ lowerCellAverage (cylinderCoefficient epsilon A b) ha k v :=
    div_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Nat.cast_nonneg _)
  refine le_trans (Real.rpow_le_rpow h0 h2 (by positivity)) ?_
  have hfm : Real.rpow (((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η)
          (fun x => (cylinderCoefficient epsilon A b x)⁻¹)‖ v) /
      ((triangulation (d := d) k).card : ℝ)) (1 / v) =
      finitePowerMean (fun η : SimplexIndex d k =>
        ‖volumeAverageMat (simplexCell k η)
          (fun x => (cylinderCoefficient epsilon A b x)⁻¹)‖) v := by
    simp [finitePowerMean, SimplexIndex]
  refine le_trans (le_of_eq hfm) ?_
  exact optimalPowers_finitePowerMean_le hv (inv_nonneg.2 hb0.le) _ _ (fun _ => norm_nonneg _)
    (fun η => (cylinderResponseFraction_bounds (hfin η) epsilon).1)
    (fun η => optimalPowers_avg_norm_lower hd (hfin η) (hvol η) epsilon hA hb0 hb1)

end

end CoarseDeGiorgi.SharpnessExamples
