import CoarseDeGiorgi.Statements.WhitneyFreeValue
import CoarseDeGiorgi.Statements.WhitneyInterpolationDef

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- The piecewise affine
extension `L_h f` of Section `s.whitney.extension`: the interpolant of Lemma `l.whitney.interpolation` of the values
`whitneyFreeValue` at the free vertices.  Meaningful on `ℝ^d ∖ τ□̄₀` (it is `0` on `τ□̄₀`
by the normalization of `IsWhitneyInterpolant`). -/
noncomputable def whitneyAffineExtension {d : ℕ} (τ h : ℝ) (f : Vec d → ℝ)
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1) : Vec d → ℝ :=
  whitneyInterpolation hτ0 hτ1 (whitneyFreeValue τ h f)

end CoarseDeGiorgi
