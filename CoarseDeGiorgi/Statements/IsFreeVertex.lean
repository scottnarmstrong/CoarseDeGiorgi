import CoarseDeGiorgi.Statements.IsWhitneyVertex

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- A vertex of a Whitney simplex is *free* if it is a vertex of every Whitney
simplex whose closure contains it. -/
def IsFreeVertex {d : ℕ} (τ : ℝ) (z : Vec d) : Prop :=
  IsWhitneyVertex τ z ∧
    ∀ cell : ExteriorCell d τ, z ∈ closure (exteriorCellSet cell) →
      ∃ j : Fin (d + 1), exteriorCellVertex cell j = z

end CoarseDeGiorgi
