import CoarseDeGiorgi.Statements.NormalizedLpMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace CoarseDeGiorgi.Harnack.Calculus

open Homogenization MeasureTheory
open scoped ENNReal

/-- `normalizedLpMoment` unfolds to the normalized integral `(|V|⁻¹ ∫_V |u|^b)^(1/b)`. -/
theorem normalizedLpMoment_eq_literal_integral {d : ℕ} (V : Set (Vec d))
    (u : Vec d → ℝ) {b : ℝ} (hb : 0 < b) :
    CoarseDeGiorgi.normalizedLpMoment b hb V u =
      ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |u x|) ^ b) ^ (1 / b) := by
  rfl

end CoarseDeGiorgi.Harnack.Calculus
