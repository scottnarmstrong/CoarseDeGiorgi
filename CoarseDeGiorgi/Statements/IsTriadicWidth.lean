module

public import CoarseDeGiorgi.Statements.OriginCube

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

def IsTriadicWidth (h : ℝ) : Prop :=
  ∃ n : ℕ, h = (3 : ℝ) ^ (-(n : ℤ))

end CoarseDeGiorgi
