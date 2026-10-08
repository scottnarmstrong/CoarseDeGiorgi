import Homogenization.Ambient.CoefficientField
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Support
import CoarseDeGiorgi.Statements.AuxCube
import CoarseDeGiorgi.Statements.OriginCube

open Homogenization MeasureTheory

namespace CoarseDeGiorgi

/-- Structural part of Proposition `p.fractional.localization`: a finite collection `S` of pairs
`(m, z)`, read as the threefold enlargement `auxCube m z = z 3^{-m} + □_{1-m}` of the triadic cube
`z 3^{-m} + □_{-m}`, with `Q ⋐ ρ₂□₀` (closure in `originCube ρ₂`), together with nonnegative functions
`φ_i ∈ C_c^∞(Q_i)`. -/
def IsFractionalCover {d : ℕ} (ρ₂ : ℝ) (S : Finset (ℤ × (Fin d → ℤ)))
    (φ : ℤ × (Fin d → ℤ) → Vec d → ℝ) : Prop :=
  ∀ i ∈ S,
    closure (auxCube i.1 i.2) ⊆ originCube ρ₂ ∧
    ContDiff ℝ (⊤ : ℕ∞) (φ i) ∧
    HasCompactSupport (φ i) ∧
    tsupport (φ i) ⊆ auxCube i.1 i.2 ∧
    ∀ x, 0 ≤ φ i x

end CoarseDeGiorgi
