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
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.GammaCacc
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.WeightedEnergy

public import CoarseDeGiorgi.Endpoint.Completion.NarrowWidths
public import CoarseDeGiorgi.CgCaccioppoli.Final

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.cg.caccioppoli`, estimate `e.cg.caccioppoli`.  `γ₂ = gammaCacc`,
`σ = sigmaUpper`, `Θ = contrast` (no `1 +`). -/
theorem caccioppoli_inequality :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
          spatialMomentRange a ha p q s t →
          ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ v x) →
            (hv : IsWeightedSubsolution a (originCube 1) v G) →
            ∀ ρ₁ ρ₂ : ℝ, (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              weightedEnergy a (originCube ρ₁) G ≤
                C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaCacc d p q s t) *
                  upperMoment a ha s p hs (le_of_lt hp) *
                  ENNReal.rpow (contrast a ha s t p q hs ht
                    (le_of_lt hp) (le_of_lt hq))
                    (sigmaUpper d p s / paramTheta d p q s t) *
                  ENNReal.rpow
                    (eLpNorm v 2 (volume.restrict (originCube ρ₂))) 2
:=
  CgCaccioppoli.caccioppoli_inequality_of_energy Endpoint.good_radius_energy_narrow

end CoarseDeGiorgi
