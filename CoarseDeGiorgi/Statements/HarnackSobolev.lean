module

public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.OriginCube
public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.NegSobolevNorm
public import CoarseDeGiorgi.Statements.IsOpenOriginCube

public import CoarseDeGiorgi.NegSobolev.CorollarySobolev
public import CoarseDeGiorgi.Statements.MomentBoundsSobolev

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Corollary E (`c.sobolev.coefficients`), the Harnack inequality
(e.sobolev.harnack): under the hypotheses of `local_boundedness_sobolev` (`d ≥ 3`,
`1 < p, q < ∞`, `α, β ≥ 0`, `θ > 0`, standing hypotheses on `□₀`, finite norms
`‖a‖_{W^{-α,p}(□₀)}`, `‖a⁻¹‖_{W^{-β,q}(□₀)}` with `|a|, |a⁻¹| ∈ L¹(□₀)`) there is
`C = C(d, p, q, α, β)` such that every nonnegative solution `u ∈ Csol(□₀)` (gradient witness `G`)
satisfies `ess sup_{½□₀} u ≤ exp(C (‖a‖_{W^{-α,p}(□₀)} ‖a⁻¹‖_{W^{-β,q}(□₀)})^{1/2}) ess inf_{½□₀} u`.
The shape follows `harnack`. -/
theorem harnack_sobolev (d : ℕ) (_hd : 3 ≤ d) (p q α β : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (θ : ℝ) (_hθdef : θ = 1 - (α + β) / 2 - ((d : ℝ) - 1) / 2 * (1 / p + 1 / q))
    (_hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffField d), IsWeightedCoeffOn (originCube 1) a →
      ∀ (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1))),
        negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp < ⊤ →
        negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq < ⊤ →
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
        IsWeightedSolution a (originCube 1) u G →
        eLpNorm u ⊤ (volume.restrict (originCube (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt
            (negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq).toReal)) *
            nonnegativeEssInf (originCube (1 / 2)) u
:=
  by exact CoarseDeGiorgi.NegSobolev.harnack_sobolev_of_moment_bounds CoarseDeGiorgi.moment_bounds_sobolev d _hd p q α β hp hq hα hβ θ _hθdef _hθ

end CoarseDeGiorgi
