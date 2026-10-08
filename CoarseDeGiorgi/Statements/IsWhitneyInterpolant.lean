import CoarseDeGiorgi.Statements.IsFreeVertex
import CoarseDeGiorgi.Statements.ClosedReferenceCube
import CoarseDeGiorgi.Statements.SmoothGrad

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The conditions of Lemma `l.whitney.interpolation`: `g` is continuous on `ℝ^d ∖ τ□̄₀`, affine on
every Whitney simplex, and attains the prescribed values at the free vertices.  Functions on the
exterior are encoded as `Vec d → ℝ`; the extra normalization `g = 0` on `τ□̄₀` only fixes the
irrelevant values off the exterior, so that uniqueness is literal. -/
def IsWhitneyInterpolant {d : ℕ} (τ : ℝ) (vals : {z : Vec d // IsFreeVertex τ z} → ℝ)
    (g : Vec d → ℝ) : Prop :=
  (∀ x ∈ closedReferenceCube (d := d) τ, g x = 0) ∧
  ContinuousOn g (closedReferenceCube (d := d) τ)ᶜ ∧
  (∀ cell : ExteriorCell d τ, ∃ (e : Vec d) (c : ℝ),
    ∀ x ∈ exteriorCellSet cell, g x = vecDot e x + c) ∧
  (∀ z : {z : Vec d // IsFreeVertex τ z}, g z.1 = vals z)

end CoarseDeGiorgi
