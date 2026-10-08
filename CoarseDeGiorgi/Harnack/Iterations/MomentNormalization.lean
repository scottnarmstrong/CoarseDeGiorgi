import CoarseDeGiorgi.Harnack.Iterations.NormalizedMomentOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- The normalized moment `normalizedLpMoment` is the volume-normalized finite-exponent seminorm.
-/
theorem normalizedLpMoment_eq_eLpNorm {d : ℕ} (V : Set (Vec d))
    (f : Vec d → ℝ) {b : ℝ} (hb : 0 < b)
    (hf : AEStronglyMeasurable f (volume.restrict V)) :
    normalizedLpMoment b hb V f =
      (volume V) ^ (-(1 / b)) * eLpNorm f (ENNReal.ofReal b) (volume.restrict V) := by
  rw [normalizedLpMoment_eq_eLpNorm' V f hb]
  have h := eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.mpr hb).ne'
    ENNReal.ofReal_ne_top hf
  rw [ENNReal.toReal_ofReal hb.le] at h
  rw [h]
  simp only [Measure.restrict_apply_univ]
  congr 2
  ring

/-- On domains of volume at most one, a stopped normalized moment of order at
least one controls the unnormalized first moment on every subset.
-/
theorem eLpNorm_one_le_stopped_normalizedMoment {d : ℕ}
    (E V : Set (Vec d)) (f : Vec d → ℝ) {q : ℝ}
    (hq : 1 ≤ q) (hEV : E ⊆ V)
    (hf : AEStronglyMeasurable f (volume.restrict V))
    (hEvol : volume E ≤ 1) (hVpos : 0 < volume V) (hVvol : volume V ≤ 1) :
    eLpNorm f 1 (volume.restrict E) ≤
      normalizedLpMoment q (zero_lt_one.trans_le hq) V f := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hfE := hf.mono_measure (Measure.restrict_mono hEV le_rfl)
  have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal q by
      simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq) hfE
  have hexp : 0 ≤ 1 - 1 / q := by
    have hinv : 1 / q ≤ 1 := (div_le_iff₀ hqpos).2 (by simpa using hq)
    linarith
  have hcompare' : eLpNorm f 1 (volume.restrict E) ≤
      eLpNorm f (ENNReal.ofReal q) (volume.restrict E) := by
    have hfactor : (volume E) ^ (1 - 1 / q) ≤ 1 :=
      ENNReal.rpow_le_one hEvol hexp
    have h := mul_le_mul_of_nonneg_left hfactor
      (by positivity : 0 ≤ eLpNorm f (ENNReal.ofReal q) (volume.restrict E))
    have hcompare'' : eLpNorm f 1 (volume.restrict E) ≤
        eLpNorm f (ENNReal.ofReal q) (volume.restrict E) *
          (volume E) ^ (1 - 1 / q) := by
      simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal hqpos.le,
        one_div_one, Measure.restrict_apply_univ] using hcompare
    exact hcompare''.trans (by simpa using h)
  have hVtop : volume V ≠ ⊤ := (hVvol.trans_lt ENNReal.one_lt_top).ne
  have hnorm : eLpNorm f (ENNReal.ofReal q) (volume.restrict V) ≤
      normalizedLpMoment q hqpos V f := by
    rw [normalizedLpMoment_eq_eLpNorm V f hqpos hf]
    have hfactor : 1 ≤ (volume V) ^ (-(1 / q)) := by
      have h := ENNReal.rpow_le_one hVvol (by positivity : 0 ≤ 1 / q)
      have hc : (volume V) ^ (1 / q) * (volume V) ^ (-(1 / q)) = 1 := by
        rw [← ENNReal.rpow_add _ _ hVpos.ne' hVtop]
        simp
      calc
        1 = (volume V) ^ (1 / q) * (volume V) ^ (-(1 / q)) := hc.symm
        _ ≤ 1 * (volume V) ^ (-(1 / q)) := mul_le_mul_of_nonneg_right h zero_le
        _ = _ := one_mul _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor
      (by positivity : 0 ≤ eLpNorm f (ENNReal.ofReal q) (volume.restrict V))
  exact hcompare'.trans ((eLpNorm_mono_measure f
    (Measure.restrict_mono hEV le_rfl)).trans hnorm)

end CoarseDeGiorgi.Harnack.Iterations
