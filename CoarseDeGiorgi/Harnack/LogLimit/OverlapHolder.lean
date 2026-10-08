module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace CoarseDeGiorgi.Harnack.LogLimit

open MeasureTheory
open scoped ENNReal BigOperators Topology

noncomputable section

/-- On a finite measure space, an `L^r` bound with `r > 1` controls the
integral of the absolute value by Hölder's inequality. -/
theorem integral_norm_le_of_eLpNorm_finite {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {r : ℝ}
    (hr : 1 < r)
    (hbound : eLpNorm f (ENNReal.ofReal r) μ < ⊤) :
    Integrable f μ ∧
      MeasureTheory.integral μ (fun x => ‖f x‖) ≤
        (eLpNorm f (ENNReal.ofReal r) μ).toReal *
          (μ Set.univ).toReal ^ (1 - 1 / r) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hrle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa using (ENNReal.ofReal_le_ofReal hr.le)
  have hmemr : MemLp f (ENNReal.ofReal r) μ := by
    rw [memLp_iff]
    exact hbound
  have hmem1 : MemLp f 1 μ := hmemr.mono_exponent hrle
  have hint : Integrable f μ := memLp_one_iff_integrable.mp hmem1
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (f := f) (p := 1) (q := ENNReal.ofReal r) hrle hmemr.aestronglyMeasurable
  have hmass : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hpowexp : 0 ≤ 1 - 1 / r := by
    have hfrac : 1 / r ≤ 1 := by
      rw [div_le_one hr0]
      exact hr.le
    linarith
  have hpowtop : (μ Set.univ) ^ (1 - 1 / r) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hpowexp (measure_ne_top μ _)
  have hcompare' : eLpNorm f 1 μ ≤
      eLpNorm f (ENNReal.ofReal r) μ * (μ Set.univ) ^ (1 - 1 / r) := by
    simpa [hmass] using hcompare
  have hcompareReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hmemr.eLpNorm_lt_top.ne hpowtop) hcompare'
  have hnorm : MeasureTheory.integral μ (fun x => ‖f x‖) =
      (eLpNorm f 1 μ).toReal := by
    rw [integral_norm_eq_lintegral_enorm hmem1.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hmem1.aestronglyMeasurable]
  refine ⟨hint, ?_⟩
  rw [hnorm]
  calc
    (eLpNorm f 1 μ).toReal ≤
        (eLpNorm f (ENNReal.ofReal r) μ *
          (μ Set.univ) ^ (1 - 1 / r)).toReal := hcompareReal
    _ = (eLpNorm f (ENNReal.ofReal r) μ).toReal *
        (μ Set.univ).toReal ^ (1 - 1 / r) := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
    _ ≤ (eLpNorm f (ENNReal.ofReal r) μ).toReal *
        (μ Set.univ).toReal ^ (1 - 1 / r) := le_rfl

/-- A local `L^r` bound gives the source-form overlap deviation estimate. -/
theorem integral_abs_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {r B : ℝ}
    (hr : 1 < r) (hB : 0 ≤ B)
    (hbound : eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal B) :
    Integrable f μ ∧
      MeasureTheory.integral μ (fun x => ‖f x‖) ≤
        B * (μ Set.univ).toReal ^ (1 - 1 / r) := by
  obtain ⟨hint, hest⟩ := integral_norm_le_of_eLpNorm_finite hr
    (hbound.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hint, ?_⟩
  have hnorm : (eLpNorm f (ENNReal.ofReal r) μ).toReal ≤ B := by
    calc
      _ ≤ (ENNReal.ofReal B).toReal := ENNReal.toReal_mono
        (ENNReal.ofReal_ne_top) hbound
      _ = B := ENNReal.toReal_ofReal hB
  calc
    ∫ x, |f x| ∂μ ≤ (eLpNorm f (ENNReal.ofReal r) μ).toReal *
      (μ Set.univ).toReal ^ (1 - 1 / r) := hest
    _ ≤ B * (μ Set.univ).toReal ^ (1 - 1 / r) := by
      apply mul_le_mul_of_nonneg_right hnorm
      positivity

end

end CoarseDeGiorgi.Harnack.LogLimit
