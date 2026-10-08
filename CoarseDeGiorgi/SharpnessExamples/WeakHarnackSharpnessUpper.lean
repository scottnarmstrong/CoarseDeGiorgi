module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessMoments

/-! # Finiteness of the upper moment of the weak Harnack field -/

@[expose] public section

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem volumeAverage_le_const {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (hfin : volume U ≠ ⊤) (hpos : volume U ≠ 0) {f : Vec d → ℝ} (hf : IntegrableOn f U)
    {M : ℝ} (hM : ∀ x ∈ U, f x ≤ M) : volumeAverage U f ≤ M := by
  unfold volumeAverage
  have hvpos : 0 < (volume U).toReal := ENNReal.toReal_pos hpos hfin
  have h1 : ∫ x in U, f x ≤ ∫ x in U, M :=
    setIntegral_mono_on hf (integrableOn_const hfin) hU hM
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h1
  calc (volume U).toReal⁻¹ * ∫ x in U, f x ≤ (volume U).toReal⁻¹ * ((volume U).toReal * M) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hvpos.le)
    _ = M := by field_simp

theorem simplexCell_volume_pos {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    volume (simplexCell k η) ≠ 0 := by
  intro h0
  have := Assembly.ClassicalMomentsImpl.simplexCell_volume_real (d := d) k η
  rw [h0] at this
  simp only [ENNReal.toReal_zero] at this
  have hN : (0 : ℝ) < ((triangulation (d := d) k).card : ℝ) :=
    Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)
  exact (inv_pos.mpr hN).ne this

theorem simplexCell_volume_ne_top {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    volume (simplexCell k η) ≠ ⊤ :=
  (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne

theorem simplexCell_measurableSet {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    MeasurableSet (simplexCell k η) :=
  (simplexCell_isOpenBoundedConvexDomain k η).isOpen.measurableSet

theorem whUpperMoment_lt_top {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t)
    {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p)
    (ha : IsWeightedCoeffOn (originCube (d := d) 1) (whCoeff d q t)) :
    upperMoment (whCoeff d q t) ha s p hs hp < ⊤ := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  set Mb : ℝ := (Real.exp 1 * whR d) ^ whBeta d q t / (whBeta d q t / 3) ^ 3 with hMb
  have hMb0 : 0 ≤ Mb := div_nonneg (Real.rpow_nonneg (mul_nonneg (Real.exp_pos 1).le (whR_pos hd).le) _) (by positivity)
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hlev : ∀ k : ℕ, upperCellAverage (whCoeff d q t) ha k p ≤ Mb ^ p := by
    intro k
    have h1 := Besov.upperCellAverage_le_matrixCellPowerAverage (whCoeff d q t) ha k p hp
    have h2 : upperCellAverage (whCoeff d q t) ha k p ≤
        ((triangulation (d := d) k).attach.sum fun η =>
          Real.rpow ‖volumeAverageMat (simplexCell k η) (whCoeff d q t)‖ p) /
        ((triangulation (d := d) k).card : ℝ) := h1
    refine h2.trans ?_
    have hN : (0 : ℝ) < ((triangulation (d := d) k).card : ℝ) :=
      Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)
    rw [div_le_iff₀ hN]
    calc ((triangulation (d := d) k).attach.sum fun η =>
          Real.rpow ‖volumeAverageMat (simplexCell k η) (whCoeff d q t)‖ p)
        ≤ (triangulation (d := d) k).attach.sum (fun _ => Mb ^ p) := by
          refine Finset.sum_le_sum (fun η _ => ?_)
          have hn : ‖volumeAverageMat (simplexCell k η) (whCoeff d q t)‖ =
              volumeAverage (simplexCell k η) (fun x => whField d q t (euclidNorm x)) :=
            norm_volumeAverageMat_scalar_identity _ _ (fun x => whField_nonneg _ _ _ _)
          rw [hn]
          have hle : volumeAverage (simplexCell k η) (fun x => whField d q t (euclidNorm x)) ≤ Mb :=
            volumeAverage_le_const (simplexCell_measurableSet k η) (simplexCell_volume_ne_top k η)
              (simplexCell_volume_pos k η)
              ((whWeight_integrable hβ).mono_set (CoarseDeGiorgi.simplexCell_subset_originCube k η))
              (fun x hx => whField_le hd hβ (euclidNorm_nonneg' x)
                (norm_lt_R_of_mem (CoarseDeGiorgi.simplexCell_subset_originCube k η hx)))
          have hnn : 0 ≤ volumeAverage (simplexCell k η) (fun x => whField d q t (euclidNorm x)) := by
            unfold volumeAverage
            exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
              (integral_nonneg (fun x => whField_nonneg _ _ _ _))
          exact Real.rpow_le_rpow hnn hle hp0.le
      _ = ((triangulation (d := d) k).card : ℝ) * Mb ^ p := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = Mb ^ p * ((triangulation (d := d) k).card : ℝ) := mul_comm _ _
  -- the series
  set C : ℝ≥0∞ := (ENNReal.ofReal (Mb ^ p)).rpow (1 / (2 * p)) with hC
  have hCtop : C < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hgeom : (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s)))) < ⊤ := by
    have hσ : Real.rpow 3 (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hσ0 : 0 ≤ Real.rpow 3 (-s) := Real.rpow_nonneg (by norm_num) _
    have heq : ∀ k : ℕ, Real.rpow 3 (-((k : ℝ) * s)) = (Real.rpow 3 (-s)) ^ k := by
      intro k
      change (3 : ℝ) ^ (-((k : ℝ) * s)) = ((3 : ℝ) ^ (-s)) ^ k
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    simp_rw [heq]
    exact (summable_geometric_of_lt_one hσ0 hσ).tsum_ofReal_lt_top
  unfold upperMoment
  refine ENNReal.pow_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  calc (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal (upperCellAverage (whCoeff d q t) ha k p)).rpow (1 / (2 * p)))
      ≤ ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * C := by
        refine ENNReal.tsum_le_tsum (fun k => ?_)
        exact mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hlev k))
          (by positivity)) _
    _ = (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s)))) * C := ENNReal.tsum_mul_right
    _ < ⊤ := ENNReal.mul_lt_top hgeom hCtop

end

end CoarseDeGiorgi.SharpnessExamples
