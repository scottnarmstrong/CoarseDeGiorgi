import CoarseDeGiorgi.Statements.WhitneyCubes

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

def ExteriorCell (d : ℕ) (τ : ℝ) :=
  {D : TriadicCube d // D ∈ whitneyCubes τ} ×
    ((Fin d → Fin 3) × Equiv.Perm (Fin d))

end CoarseDeGiorgi
