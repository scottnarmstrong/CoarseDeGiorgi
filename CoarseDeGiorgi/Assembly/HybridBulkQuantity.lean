import CoarseDeGiorgi.Assembly.HybridFractional
import CoarseDeGiorgi.Assembly.HybridInner
import CoarseDeGiorgi.Assembly.HybridQuantity
import CoarseDeGiorgi.Weighted.Truncation.PositivePart

namespace CoarseDeGiorgi.Assembly
open Homogenization MeasureTheory Set Filter
open scoped ENNReal

/-- The literal identity between the two positive truncation levels. -/
theorem hybrid_positive_level_identity {x a b : ℝ} (hab : a ≤ b) :
    max (max (x - a) 0 - (b - a)) 0 = max (x - b) 0 := by
  by_cases hx : x ≤ a
  · rw [max_eq_right (sub_nonpos.mpr hx), max_eq_right (by linarith only [hab])]
    exact (max_eq_right (sub_nonpos.mpr (hx.trans hab))).symm
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hx))]
    congr 1
    ring

end CoarseDeGiorgi.Assembly
