module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessUpper

/-! # The level estimate for the lower moment of the weak Harnack field -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The reciprocal field as a smul of the identity. -/
theorem whCoeff_inv {d : ℕ} (q t : ℝ) (x : Vec d) :
    (whCoeff d q t x)⁻¹ = (whField d q t (euclidNorm x))⁻¹ • (1 : Mat d) := by
  unfold whCoeff
  exact smul_one_inv _

theorem whW2_integrable {d : ℕ} [NeZero d] {β h q : ℝ} (hβ : 0 ≤ β) (hq : 0 ≤ q) (h0 : 0 < h) :
    IntegrableOn (fun x : Vec d => whFar β h ‖x‖) (originCube 1) ∧
    IntegrableOn (fun x : Vec d => whFar β h ‖x‖ ^ q) (originCube 1) := by
  have hm : Measurable (fun x : Vec d => whFar β h ‖x‖) :=
    (measurable_whFar β h).comp measurable_norm
  constructor
  · refine Measure.integrableOn_of_bounded (M := h ^ (-β)) volume_originCube_ne_top
      hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_of_nonneg (whFar_nonneg _ _ (norm_nonneg x))]
    exact whFar_le hβ h0
  · refine Measure.integrableOn_of_bounded (M := (h ^ (-β)) ^ q) volume_originCube_ne_top
      (hm.pow_const q).aestronglyMeasurable (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (whFar_nonneg _ _ (norm_nonneg x)) _)]
    exact Real.rpow_le_rpow (whFar_nonneg _ _ (norm_nonneg x)) (whFar_le hβ h0) hq

theorem whNear_integrableOn {d : ℕ} [NeZero d] {β h : ℝ} (hβd : β < d) (h0 : 0 < h)
    (h1 : h ≤ 1) : IntegrableOn (fun x : Vec d => whNear β h ‖x‖) (originCube 1) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  exact ((integrable_polar_pi (d := d) (f := whNear β h)).2
    (near_integral hd hβd h0 h1).1).integrableOn

theorem whLower_level_le {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t)
    (hβd : whBeta d q t < d) (hq : 1 ≤ q) {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1)
    (ha : IsWeightedCoeffOn (originCube (d := d) 1) (whCoeff d q t)) (k : ℕ) :
    lowerCellAverage (whCoeff d q t) ha k q ≤
      2 ^ q * (((triangulation (d := d) k).card : ℝ) ^ (q - 1) *
        (∫ x in originCube (d := d) 1, whNear (whBeta d q t) h ‖x‖) ^ q +
        ∫ x in originCube (d := d) 1, whFar (whBeta d q t) h ‖x‖ ^ q) := by
  classical
  set β := whBeta d q t with hβdef
  have hq0 : 0 ≤ q := by linarith
  have hW1 := whNear_integrableOn (d := d) hβd h0 h1
  obtain ⟨hW2, hW2q⟩ := whW2_integrable (d := d) (β := β) (h := h) (q := q) hβ.le hq0 h0
  have h1' := Besov.lowerCellAverage_le_matrixCellPowerAverage (whCoeff d q t) ha k q hq
  have h2 : lowerCellAverage (whCoeff d q t) ha k q ≤
      ((triangulation (d := d) k).attach.sum fun η =>
        Real.rpow ‖volumeAverageMat (simplexCell k η) (fun x => (whCoeff d q t x)⁻¹)‖ q) /
      ((triangulation (d := d) k).card : ℝ) := h1'
  refine h2.trans ?_
  have hN : (0 : ℝ) < ((triangulation (d := d) k).card : ℝ) :=
    Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)
  refine le_trans ?_ (level_power_mean_le k hq _ _
    (fun x => whNear_nonneg β h (norm_nonneg x) h1) (fun x => whFar_nonneg β h (norm_nonneg x))
    hW1 hW2 hW2q)
  apply div_le_div_of_nonneg_right _ hN.le
  refine Finset.sum_le_sum (fun η _ => ?_)
  have hsub := CoarseDeGiorgi.simplexCell_subset_originCube (d := d) k η
  have hn : ‖volumeAverageMat (simplexCell k η) (fun x => (whCoeff d q t x)⁻¹)‖ =
      volumeAverage (simplexCell k η) (fun x => (whField d q t (euclidNorm x))⁻¹) := by
    simp_rw [whCoeff_inv]
    exact norm_volumeAverageMat_scalar_identity _ _
      (fun x => inv_nonneg.2 (whField_nonneg _ _ _ _))
  rw [hn]
  have hnn : 0 ≤ volumeAverage (simplexCell k η) (fun x => (whField d q t (euclidNorm x))⁻¹) := by
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg (fun x => inv_nonneg.2 (whField_nonneg _ _ _ _)))
  refine Real.rpow_le_rpow hnn ?_ (by linarith)
  unfold volumeAverage
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ENNReal.toReal_nonneg)
  refine setIntegral_mono_on ((whInv_integrable hβ hβd).mono_set hsub)
    ((hW1.add hW2).mono_set hsub) (simplexCell_measurableSet k η) (fun x hx => ?_)
  exact whField_inv_le hβ (hsub hx) h1

end

end CoarseDeGiorgi.SharpnessExamples
