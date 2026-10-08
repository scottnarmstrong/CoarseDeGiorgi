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
public import CoarseDeGiorgi.Statements.FracSeminorm
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.SimplexCell
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.TriangulationIn
public import CoarseDeGiorgi.Statements.WeightedEnergy

public import CoarseDeGiorgi.LowerFractional.CubeFinal

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.lower.fractional`, the scale-by-scale bound `e.lower.fractional.local`: for
`n ∈ ℕ₀`, `Q = auxCube (n+1) z = 3^{-n-1} z + □₋ₙ ⊆ □₀` and `w ∈ H¹_a(Q)`, the `W^{1-t,r}(Q)` seminorm is at most
`C ℰ_Q(w)^{1/2} ∑_{k>n} 3^{-kt} (∑_{△ ∈ 𝒯_k(Q)} |△| |a_*^{-1}(△)|^q)^{1/(2q)}`, with `C = C(d, q, t)`. -/
theorem lower_fractional_scale_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ q t : ℝ, 1 < q → 0 < t →
      ∃ C : ℝ, 0 < C ∧
        ∀ p s : ℝ, 1 < p → 0 < s →
          ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
            spatialMomentRange a ha p q s t →
            ∀ (n : ℕ) (z : Fin d → ℤ) (w : Vec d → ℝ) (G : Vec d → Vec d),
              auxCube ((n : ℤ) + 1) z ⊆ originCube 1 →
              MemH1a a (auxCube ((n : ℤ) + 1) z) w G →
              fracSeminorm (auxCube ((n : ℤ) + 1) z) (alphaParam t) (paramR q) w ≤
                ENNReal.ofReal C *
                  (weightedEnergy a (auxCube ((n : ℤ) + 1) z) G).rpow (1 / 2) *
                  ∑' k : ℕ,
                    if n < k then
                      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
                        (∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
                          volume (simplexCell k η) *
                            ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)).rpow
                          (1 / (2 * q))
                    else 0
:=
  LowerFractional.lower_fractional_scale_bound_of_reconstruction LowerFractional.cube_reconstruction

end CoarseDeGiorgi
