import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicMeasure
import CoarseDeGiorgi.Foundations.Reconstruction.WrapDistance

/-! # Periodic sup-norm support envelopes with both integral bounds -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Fine envelopes use a single wrapped compact box, with no periodization series. -/
def periodicEnvelope (m : ℤ) (h : ℝ) (v : Vec d) : ℝ≥0∞ :=
  (ENNReal.ofReal (h ^ d))⁻¹ *
    (Metric.closedBall (0 : Vec d) (3 * h)).indicator (fun _ => 1) (wrapBox m v)

theorem measurable_periodicEnvelope (m : ℤ) (h : ℝ) :
    Measurable (periodicEnvelope (d := d) m h) :=
  measurable_const.mul ((measurable_const.indicator measurableSet_closedBall).comp
    (measurable_wrapBox m))

theorem periodicEnvelope_add_period (m : ℤ) (h : ℝ) (i : Fin d) (v : Vec d) :
    periodicEnvelope m h (v + (2 * auxSide m) • basisVec i) = periodicEnvelope m h v := by
  unfold periodicEnvelope
  rw [wrapBox_add_period_basisVec]

theorem periodicEnvelope_eq_of_norm_le (m : ℤ) (h : ℝ) {v : Vec d}
    (hv : ‖wrapBox m v‖ ≤ 3 * h) :
    periodicEnvelope m h v = (ENNReal.ofReal (h ^ d))⁻¹ := by
  rw [periodicEnvelope, Set.indicator_of_mem (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hv), mul_one]

theorem measurableSet_reflectionBox (m : ℤ) : MeasurableSet (reflectionBox (d := d) m) := by
  simp only [reflectionBox, ← Set.iInter_ofPred]
  exact MeasurableSet.iInter fun i =>
    (isOpen_lt (continuous_apply i).abs continuous_const).measurableSet

theorem volume_reflectionBox (m : ℤ) :
    volume (reflectionBox (d := d) m) = ENNReal.ofReal ((2 * auxSide m) ^ d) := by
  have heq : reflectionBox (d := d) m = Set.univ.pi (fun _ => Ioo (-auxSide m) (auxSide m)) := by
    ext x
    simp only [reflectionBox, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ioo, abs_lt]
  have hL := auxSide_pos m
  rw [heq, Real.volume_pi_Ioo]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * auxSide m)]

/-- The envelope mass is bounded uniformly in the period and physical length. -/
theorem lintegral_periodicEnvelope_le {m : ℤ} {h : ℝ} (hh : 0 < h) :
    ∫⁻ v in reflectionBox m, periodicEnvelope (d := d) m h v ≤ ENNReal.ofReal ((6 : ℝ) ^ d) := by
  have hmeas : Measurable (fun v : Vec d =>
      (Metric.closedBall (0 : Vec d) (3 * h)).indicator (fun _ => (1 : ℝ≥0∞)) v) :=
    measurable_const.indicator measurableSet_closedBall
  have heq : ∫⁻ v in reflectionBox m,
      (Metric.closedBall (0 : Vec d) (3 * h)).indicator (fun _ => (1 : ℝ≥0∞)) (wrapBox m v) =
      ∫⁻ v in reflectionBox m,
        (Metric.closedBall (0 : Vec d) (3 * h)).indicator (fun _ => (1 : ℝ≥0∞)) v := by
    apply setLIntegral_congr_fun (measurableSet_reflectionBox m)
    intro v hv
    dsimp only
    rw [wrapBox_eq_self m hv]
  have hmwrap : Measurable (fun v : Vec d =>
      (Metric.closedBall (0 : Vec d) (3 * h)).indicator (fun _ => (1 : ℝ≥0∞)) (wrapBox m v)) :=
    hmeas.comp (measurable_wrapBox m)
  simp only [periodicEnvelope]
  rw [lintegral_const_mul _ hmwrap, heq,
    lintegral_indicator measurableSet_closedBall, setLIntegral_one]
  calc
    _ ≤ (ENNReal.ofReal (h ^ d))⁻¹ * volume (Metric.closedBall (0 : Vec d) (3 * h)) :=
      mul_le_mul_of_nonneg_left (Measure.restrict_apply_le _ _) bot_le
    _ = _ := by
      rw [Real.volume_pi_closedBall _ (by linarith : 0 ≤ 3 * h), Fintype.card_fin,
        show 2 * (3 * h) = 6 * h by ring, mul_pow,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (6 : ℝ) ^ d), mul_comm,
        mul_assoc, ENNReal.mul_inv_cancel
          (ENNReal.ofReal_pos.mpr (pow_pos hh d)).ne' ENNReal.ofReal_ne_top, mul_one]

/-- The row envelope integral, including every translation. -/
theorem lintegral_periodicEnvelope_sub_le {m : ℤ} {h : ℝ} (hh : 0 < h) (x : Vec d) :
    ∫⁻ y in reflectionBox m, periodicEnvelope m h (x - y) ≤ ENNReal.ofReal ((6 : ℝ) ^ d) := by
  rw [lintegral_periodicField_sub m _ (measurable_periodicEnvelope m h)
    (periodicEnvelope_add_period m h)]
  exact lintegral_periodicEnvelope_le hh

/-- The column envelope integral has the same bound. -/
theorem lintegral_periodicEnvelope_sub_right_le {m : ℤ} {h : ℝ} (hh : 0 < h) (y : Vec d) :
    ∫⁻ x in reflectionBox m, periodicEnvelope m h (x - y) ≤ ENNReal.ofReal ((6 : ℝ) ^ d) := by
  simpa only [sub_eq_add_neg] using
    (lintegral_periodicField_add m _ (measurable_periodicEnvelope m h)
      (periodicEnvelope_add_period m h) (-y)).trans_le (lintegral_periodicEnvelope_le hh)

end

end CoarseDeGiorgi.Foundations.Reconstruction
