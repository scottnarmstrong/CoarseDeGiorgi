import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.LocallyBoundedAbove
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.GammaSup
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PositivePart
import CoarseDeGiorgi.Statements.SigmaLower
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.TwoLevelQuantity

import CoarseDeGiorgi.Statements.TwoLevelRecurrence
import CoarseDeGiorgi.Recurrence.EnergyToSupremum
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.energy.to.sup`, estimate `e.energy.to.sup`.  The exponent of `(ρ₂ - ρ₁)⁻¹` is
`γ₄ = gammaSup`, and the power of `Θ` is `(d-3+2σ_*)/(4θ)`. -/
theorem energy_to_supremum :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
          spatialMomentRange a ha p q s t →
          (∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (hu : IsWeightedSubsolution a (originCube 1) u G) →
            ∀ ρ₁ ρ₂ : ℝ, (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              twoLevelQuantity a ha q t ht (le_of_lt hq) u G 0 ρ₂ < ⊤ →
              eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ₁)) ≤
                C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaSup d p q s t) *
                  ENNReal.rpow (contrast a ha s t p q hs ht
                    (le_of_lt hp) (le_of_lt hq))
                    (((d : ℝ) - 3 + 2 * sigmaLower d q t) /
                      (4 * paramTheta d p q s t)) *
                  twoLevelQuantity a ha q t ht (le_of_lt hq) u G 0 ρ₂) ∧
          (∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            IsWeightedSubsolution a (originCube 1) u G →
            LocallyBoundedAbove (originCube 1) u)
:=
  Recurrence.energy_to_supremum_of_recurrence CoarseDeGiorgi.two_level_recurrence

end CoarseDeGiorgi
