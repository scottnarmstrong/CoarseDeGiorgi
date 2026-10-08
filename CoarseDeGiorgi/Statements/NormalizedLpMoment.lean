import CoarseDeGiorgi.Statements.OriginCube
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The normalized averaged Lᵇ quantity, for b > 0, using an ENNReal lintegral.
For arbitrary V, zero or infinite volume gives zero by ENNReal conventions. -/
noncomputable def normalizedLpMoment {d : ℕ} (b : ℝ) (_hb : 0 < b)
    (V : Set (Vec d)) (u : Vec d → ℝ) : ℝ≥0∞ :=
  ((volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |u x|).rpow b).rpow (1 / b)

end CoarseDeGiorgi
