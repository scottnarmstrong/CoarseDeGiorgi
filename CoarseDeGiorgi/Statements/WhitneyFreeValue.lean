import CoarseDeGiorgi.Statements.WhitneyPatch
import CoarseDeGiorgi.Statements.IsFreeVertex
import CoarseDeGiorgi.Statements.SeedCutoff
import CoarseDeGiorgi.Statements.SurfaceMeasure

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator NNReal

namespace CoarseDeGiorgi

/-- `e.extension.definition`: the value of `L_h f` at a free vertex `z`,
`ω((|z|_∞ - τ/2)/h) ⨍_{Σ_z} f dℋ^{d-1}`. -/
noncomputable def whitneyFreeValue {d : ℕ} (τ h : ℝ) (f : Vec d → ℝ)
    (z : {z : Vec d // IsFreeVertex τ z}) : ℝ :=
  seedCutoff ((‖z.1‖ - τ / 2) / h) * ⨍ x in whitneyPatch τ z.1, f x ∂(surfaceMeasure τ)

end CoarseDeGiorgi
