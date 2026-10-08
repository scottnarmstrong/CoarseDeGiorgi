import CoarseDeGiorgi.Statements.IsWhitneyInterpolant

import CoarseDeGiorgi.Whitney.Interpolation.Unique
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Lemma `l.whitney.interpolation`, first sentence: given real values at the
free vertices there is a unique continuous function on `ℝ^d ∖ τ□̄₀`, affine on every Whitney
simplex, attaining them. -/
theorem whitney_interpolation_existsUnique {d : ℕ} {τ : ℝ}
    (hτ0 : (1 / 2 : ℝ) ≤ τ) (hτ1 : τ < 1)
    (vals : {z : Vec d // IsFreeVertex τ z} → ℝ) :
    ∃! g : Vec d → ℝ, IsWhitneyInterpolant τ vals g
:=
  Whitney.Interpolation.whitney_interpolation_existsUnique_proof hτ0 hτ1 vals

end CoarseDeGiorgi
