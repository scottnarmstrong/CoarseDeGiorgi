module

public import CoarseDeGiorgi.Statements.ExteriorCellVertex
public import CoarseDeGiorgi.Statements.ExteriorCellSet

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- A vertex of a Whitney simplex of `τ□̄₀` (Section `s.triadic.simplices`, "Free and hanging vertices"). -/
def IsWhitneyVertex {d : ℕ} (τ : ℝ) (z : Vec d) : Prop :=
  ∃ (cell : ExteriorCell d τ) (j : Fin (d + 1)), exteriorCellVertex cell j = z

end CoarseDeGiorgi
