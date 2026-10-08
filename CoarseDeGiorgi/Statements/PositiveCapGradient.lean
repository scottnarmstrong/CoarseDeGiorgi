module

public import CoarseDeGiorgi.Statements.PositiveTruncationGradient

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def positiveCapGradient {d : ℕ} (v : Vec d → ℝ)
    (G : Vec d → Vec d) (c : ℝ) (N : ℝ≥0∞) : Vec d → Vec d :=
  if N = ⊤ then positiveTruncationGradient v G c
  else fun x => if c < v x ∧ v x < c + N.toReal then G x else 0

end CoarseDeGiorgi
