module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.AlphaParam
public import CoarseDeGiorgi.Statements.AuxCube
public import CoarseDeGiorgi.Statements.FracNorm
public import CoarseDeGiorgi.Statements.H1aWeightedNorm
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.SpatialMomentRange

public import CoarseDeGiorgi.LowerFractional.CubeFinal

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.lower.fractional`: for every triadic cube `Q = auxCube m z ⊆ □₀` (the cube `3^{-m} z + □_{1-m}`; the inclusion
forces `m ≥ 1`, i.e. the paper's `n = m - 1 ∈ ℕ₀`) the embedding
`H¹_a(Q) ⊂ W^{1-t,r}(Q)` is continuous. -/
theorem lower_fractional_embedding {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t) (m : ℤ) (z : Fin d → ℤ)
    (hQ : auxCube m z ⊆ originCube 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ w : Vec d → ℝ, ∀ G : Vec d → Vec d,
        MemH1a a (auxCube m z) w G →
        fracNorm (auxCube m z) (alphaParam t) (paramR q) w ≤
          C * h1aWeightedNorm a (auxCube m z) w G
:=
  LowerFractional.lower_fractional_embedding_of_reconstruction LowerFractional.cube_reconstruction hd p q s t a ha hrange m z hQ

end CoarseDeGiorgi
