import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Statements.EuclidDist
import CoarseDeGiorgi.Statements.SeedProjection

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- `e.extension.definition`: `Σ_z = ∂(τ□₀) ∩ B(y_z, (|z|_∞ - τ/2)/(100 d))`, with `B` the open
Euclidean ball and `y_z` the coordinate projection `seedProjection`. -/
noncomputable def whitneyPatch {d : ℕ} (τ : ℝ) (z : Vec d) : Set (Vec d) :=
  cubeSurface τ ∩
    {x | euclidDist x (seedProjection τ z) < (‖z‖ - τ / 2) / (100 * (d : ℝ))}

end CoarseDeGiorgi
