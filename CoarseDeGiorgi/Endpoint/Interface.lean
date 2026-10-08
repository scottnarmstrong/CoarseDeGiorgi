import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.HarnackEtaParam

/-! Interfaces for the interior estimates in the endpoint argument.

`remoteCube ρ` is `y₀ + ρ □₋₃` with `y₀ = (34/81) e₁`, the cube `Q₁` (`ρ = 1`) and its half `Q₀`
(`ρ = 1/2`) of Step 3 of the proof of `l.source.mass`. `RemoteLocalBoundedness` is Corollary B on `Q₁`
with `η = r/4`, `ρ₁ = 1/2`, `ρ₂ = 1`, rescaled as in the paragraph "Interior estimates" of §9.5. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint

/-- The center `y₀ = (34/81) e₁` of the remote cube. -/
noncomputable def remoteCenter (d : ℕ) : Vec d := fun i => if i.val = 0 then (34 / 81 : ℝ) else 0

/-- The cube `y₀ + ρ □₋₃`. -/
def remoteCube (d : ℕ) (ρ : ℝ) : Set (Vec d) :=
  {x | x - remoteCenter d ∈ originCube (ρ * (3 : ℝ) ^ (-3 : ℤ))}

/-- Corollary B on `Q₁ = y₀ + □₋₃` with `η = r/4`, from `Q₁` to `Q₀ = y₀ + ½□₋₃`, for nonnegative
solutions in `Q₁`; the coefficient field, the standing hypotheses and `Θ` are those of `□₀`. -/
def RemoteLocalBoundedness (d : ℕ) (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s)
    (ht : 0 < t) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
      upperMoment a ha s p hs hp.le < ⊤ →
      0 < lowerMoment a ha t q ht hq.le →
    ∀ (V : Vec d → ℝ) (Gv : Vec d → Vec d),
      (∀ᵐ x ∂(volume.restrict (remoteCube d 1)), 0 ≤ V x) →
      IsWeightedSolution a (remoteCube d 1) V Gv →
      eLpNorm V ⊤ (volume.restrict (remoteCube d (1 / 2))) ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
          eLpNorm V (ENNReal.ofReal (harnackEtaParam q)) (volume.restrict (remoteCube d 1))

end CoarseDeGiorgi.Endpoint
