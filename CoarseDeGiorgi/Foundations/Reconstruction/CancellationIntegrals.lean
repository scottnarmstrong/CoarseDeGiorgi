import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicCancellation
import CoarseDeGiorgi.Foundations.Reconstruction.SchurLp

/-! # Both cancellation integrals and the Euclidean Lʳ operator estimate -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A periodic envelope controls both integrals without changing variables through a cell center. -/
theorem lintegral_enveloped_kernel_le {m : ℤ} {h : ℝ} (hh : 0 < h)
    (H : Vec d → Vec d → Vec d) (C : ℝ≥0∞)
    (hbound : ∀ x y, ENNReal.ofReal (euclidNorm (H x y)) ≤
      C * periodicEnvelope m h (x - y)) :
    (∀ x, ∫⁻ y in reflectionBox m, ENNReal.ofReal (euclidNorm (H x y)) ≤
      C * ENNReal.ofReal ((6 : ℝ) ^ d)) ∧
    (∀ y, ∫⁻ x in reflectionBox m, ENNReal.ofReal (euclidNorm (H x y)) ≤
      C * ENNReal.ofReal ((6 : ℝ) ^ d)) := by
  constructor
  · intro x
    calc
      _ ≤ ∫⁻ y in reflectionBox m, C * periodicEnvelope m h (x - y) :=
        lintegral_mono (hbound x)
      _ = C * ∫⁻ y in reflectionBox m, periodicEnvelope m h (x - y) :=
        lintegral_const_mul _ ((measurable_periodicEnvelope m h).comp
          (measurable_const.sub measurable_id))
      _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_periodicEnvelope_sub_le hh x) bot_le
  · intro y
    calc
      _ ≤ ∫⁻ x in reflectionBox m, C * periodicEnvelope m h (x - y) :=
        lintegral_mono (fun x => hbound x y)
      _ = C * ∫⁻ x in reflectionBox m, periodicEnvelope m h (x - y) :=
        lintegral_const_mul _ ((measurable_periodicEnvelope m h).comp
          (measurable_id.sub_const y))
      _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_periodicEnvelope_sub_right_le hh y) bot_le

end

end CoarseDeGiorgi.Foundations.Reconstruction
