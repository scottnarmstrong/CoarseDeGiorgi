module

public import CoarseDeGiorgi.Statements.CubeSurface
public import CoarseDeGiorgi.Statements.EuclidDist
public import CoarseDeGiorgi.Statements.SeedProjection

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- `e.extension.definition`: `Σ_z = ∂(τ□₀) ∩ B(y_z, (|z|_∞ - τ/2)/(100 d))`, with `B` the open
Euclidean ball and `y_z` the coordinate projection `seedProjection`. -/
noncomputable def whitneyPatch {d : ℕ} (τ : ℝ) (z : Vec d) : Set (Vec d) :=
  cubeSurface τ ∩
    {x | euclidDist x (seedProjection τ z) < (‖z‖ - τ / 2) / (100 * (d : ℝ))}

end CoarseDeGiorgi
