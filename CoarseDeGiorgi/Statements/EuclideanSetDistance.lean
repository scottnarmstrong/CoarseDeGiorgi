import CoarseDeGiorgi.Statements.EuclidDist

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def euclideanSetDistance {d : ℕ} (S T : Set (Vec d)) : ℝ≥0∞ :=
  ⨅ x ∈ S, ⨅ y ∈ T, ENNReal.ofReal (euclidDist x y)

end CoarseDeGiorgi
