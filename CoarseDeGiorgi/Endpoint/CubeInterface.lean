import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.NormalizedLpMoment
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.HarnackEtaParam

/-! Interfaces between the rescaling and the chaining steps of §9.5 "Interior estimates".

`gridCube y ρ` is `y + ρ □₋₃`; for `y ∈ 3⁻⁴ ℤ^d` the cube `Q_y = gridCube y 1` is the threefold enlargement
of `y + □₋₄`. `LocalWeakHarnackCubes` and `LocalHarnackCubes` are `e.weak.harnack` at `η = r/4` and `e.harnack` on these
cubes, obtained from `weak_harnack` and `harnack` by the rescaling `Φ(x) = y + 3⁻³ x`; the
coefficient field, the standing hypotheses and `Θ` are those of `□₀`. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint

/-- The cube `y + ρ □₋₃`. -/
def gridCube (d : ℕ) (y : Vec d) (ρ : ℝ) : Set (Vec d) :=
  {x | x - y ∈ originCube (ρ * (3 : ℝ) ^ (-3 : ℤ))}

/-- `y ∈ 3⁻⁴ ℤ^d`. -/
def IsGridPoint (d : ℕ) (y : Vec d) : Prop := ∀ i, ∃ m : ℤ, y i = (m : ℝ) / 81

/-- `e.weak.harnack` at `η = r/4` on the cubes `Q_y = y + □₋₃ ⊆ □₀`, `y ∈ 3⁻⁴ ℤ^d`, rescaled. -/
def LocalWeakHarnackCubes (d : ℕ) (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s)
    (ht : 0 < t) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
      upperMoment a ha s p hs hp.le < ⊤ →
      0 < lowerMoment a ha t q ht hq.le →
    ∀ (y : Vec d), IsGridPoint d y → gridCube d y 1 ⊆ originCube 1 →
    ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
      (∀ᵐ x ∂(volume.restrict (gridCube d y 1)), 0 ≤ u x) →
      IsWeightedSupersolution a (gridCube d y 1) u G →
      normalizedLpMoment (harnackEtaParam q) (by
          have hq0 : 0 < q := lt_trans (by norm_num) hq
          dsimp [harnackEtaParam, paramR]
          positivity)
        (gridCube d y (5 / 8)) u ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
          nonnegativeEssInf (gridCube d y (1 / 2)) u

/-- `e.harnack` on the cubes `Q_y = y + □₋₃ ⊆ □₀`, `y ∈ 3⁻⁴ ℤ^d`, rescaled. -/
def LocalHarnackCubes (d : ℕ) (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s)
    (ht : 0 < t) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
      upperMoment a ha s p hs hp.le < ⊤ →
      0 < lowerMoment a ha t q ht hq.le →
    ∀ (y : Vec d), IsGridPoint d y → gridCube d y 1 ⊆ originCube 1 →
    ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
      (∀ᵐ x ∂(volume.restrict (gridCube d y 1)), 0 ≤ u x) →
      IsWeightedSolution a (gridCube d y 1) u G →
      eLpNorm u ⊤ (volume.restrict (gridCube d y (1 / 2))) ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
          nonnegativeEssInf (gridCube d y (1 / 2)) u

end CoarseDeGiorgi.Endpoint
