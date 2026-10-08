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
public import CoarseDeGiorgi.Statements.GammaRec
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.ParamR
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.RBoundaryParam
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.SigmaLower
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.TwoLevelQuantity

public import CoarseDeGiorgi.Endpoint.Completion.NarrowWidths
public import CoarseDeGiorgi.Recurrence.TwoLevel

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.two.level.recurrence`, estimate `e.two.level.recurrence`.  `Y_b(ρ)` is
`twoLevelQuantity ... u G b ρ`; `γ₃ = gammaRec`, `σ_* = sigmaLower`, `r^*_∂ = rBoundaryParam`,
`r^* = rStarParam`; the boundary term carries `Θ^{(1-σ_*)/θ}` (no `1 +`). -/
theorem two_level_recurrence :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
        (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
        0 < paramTheta d p q s t →
        ∃ C : ℝ≥0∞, C < ⊤ ∧
          ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
            spatialMomentRange a ha p q s t →
            ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
              (hu : IsWeightedSubsolution a (originCube 1) u G) →
              ∀ l₀ l₁ ρ₁ ρ₂ : ℝ, 0 ≤ l₀ → l₀ < l₁ →
                (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
                twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂ < ⊤ →
                ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₁ ρ₁) 2 ≤
                  ENNReal.ofReal ε₀ *
                    ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂) 2 +
                  C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaRec d p q s t) *
                    (ENNReal.rpow (contrast a ha s t p q hs ht
                        (le_of_lt hp) (le_of_lt hq))
                        ((1 - sigmaLower d q t) / paramTheta d p q s t) *
                      ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂)
                          (rBoundaryParam (d := d) q t) *
                      ENNReal.rpow (ENNReal.ofReal (l₁ - l₀))
                          (2 - rBoundaryParam (d := d) q t) +
                    ENNReal.rpow (twoLevelQuantity a ha q t ht (le_of_lt hq) u G l₀ ρ₂)
                        (2 * rStarParam (d := d) q t / paramR q) *
                      ENNReal.rpow (ENNReal.ofReal (l₁ - l₀))
                        (2 - 2 * rStarParam (d := d) q t / paramR q))
:=
  Recurrence.two_level_recurrence_of_energy Endpoint.good_radius_energy_narrow

end CoarseDeGiorgi
