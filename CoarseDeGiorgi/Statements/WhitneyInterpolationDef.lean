module

public import CoarseDeGiorgi.Statements.WhitneyInterpolationExistsUnique

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The interpolant of Lemma
`l.whitney.interpolation` (the function `g`); it is `0` on `τ□̄₀` by the normalization in `IsWhitneyInterpolant`. -/
noncomputable def whitneyInterpolation {d : ℕ} {τ : ℝ}
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) : Vec d → ℝ :=
  Classical.choose (whitney_interpolation_existsUnique hτ0 hτ1 vals).exists

end CoarseDeGiorgi
