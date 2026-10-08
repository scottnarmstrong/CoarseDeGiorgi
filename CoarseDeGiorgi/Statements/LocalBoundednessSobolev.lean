import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.PositivePart
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.NegSobolevNorm
import CoarseDeGiorgi.Statements.IsOpenOriginCube

import CoarseDeGiorgi.NegSobolev.CorollarySobolev
import CoarseDeGiorgi.Statements.MomentBoundsSobolev
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Corollary E (`c.sobolev.coefficients`), the local boundedness bound
(e.sobolev.local.boundedness): let `d ≥ 3`, `1 < p, q < ∞`, `α, β ≥ 0` and
`θ = 1 - (α + β)/2 - (d - 1)/2 (1/p + 1/q) > 0`. There are `C < ∞` and `γ > 0`, depending only on
`d, p, q, α, β`, such that for every coefficient field `a` satisfying the standing hypotheses
(e.weighted.hypotheses) on `□₀` with `a ∈ W^{-α,p}(□₀) ∩ L¹(□₀)` and
`a⁻¹ ∈ W^{-β,q}(□₀) ∩ L¹(□₀)` (finite norms e.negative.sobolev.norm), every subsolution
`u ∈ Csub(□₀)` (gradient witness `G`) satisfies, for `1/2 ≤ ρ₁ < ρ₂ ≤ 1`,
`‖u₊‖_{L^∞(ρ₁□₀)} ≤ C (ρ₂ - ρ₁)^{-γ} (‖a‖_{W^{-α,p}(□₀)} ‖a⁻¹‖_{W^{-β,q}(□₀)})^{(d-1)/(2θ)} ‖u₊‖_{L²(ρ₂□₀)}`,
with a finite right side when `ρ₂ < 1` (encoded, as in `local_boundedness`, by the finiteness of
`‖u₊‖_{L²(ρ₂□₀)}`). The shape follows the `L²` part of `local_boundedness`; `θ` is bound by an
equation as `θ₀` in `sharpness`. -/
theorem local_boundedness_sobolev (d : ℕ) (_hd : 3 ≤ d) (p q α β : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (θ : ℝ) (_hθdef : θ = 1 - (α + β) / 2 - ((d : ℝ) - 1) / 2 * (1 / p + 1 / q))
    (_hθ : 0 < θ) :
    ∃ C γ : ℝ, 0 ≤ C ∧ 0 < γ ∧
      ∀ (a : CoeffField d), IsWeightedCoeffOn (originCube 1) a →
      ∀ (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1))),
        negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp < ⊤ →
        negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq < ⊤ →
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
        IsWeightedSubsolution a (originCube 1) u G →
        ∀ (ρ₁ ρ₂ : ℝ), 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        let rhs := ENNReal.ofReal C *
          (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-γ) *
          (negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA α p hα hp *
            negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv β q hβ hq).rpow
              ((d - 1 : ℝ) / (2 * θ)) *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ₂))
        eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ₁)) ≤ rhs ∧
          (ρ₂ < 1 → eLpNorm (positivePart u) 2 (volume.restrict (originCube ρ₂)) < ⊤)
:=
  by exact CoarseDeGiorgi.NegSobolev.local_boundedness_sobolev_of_moment_bounds CoarseDeGiorgi.moment_bounds_sobolev d _hd p q α β hp hq hα hβ θ _hθdef _hθ

end CoarseDeGiorgi
