import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.NegSobolevNorm
import CoarseDeGiorgi.Statements.IsOpenOriginCube

import CoarseDeGiorgi.NegSobolev.MomentBoundsSobolev
import CoarseDeGiorgi.Statements.NegativeSobolevBound
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Theorem D(iii) (`t.coefficient.conditions`, `c.negative.sobolev`), finite
`1 < p, q < ∞`: for `s, t > 0` and `0 < ε ≤ 2 min{s, t}` (the two
hypotheses `ε ≤ 2s`, `ε ≤ 2t`) there is `C = C(d, p, q, s, t, ε)` such that, if
`‖a‖_{W^{-2s+ε,p}(□₀)}` and `‖a⁻¹‖_{W^{-2t+ε,q}(□₀)}` (e.negative.sobolev.norm) are finite,
`Λ_{s,1,p}(□₀) ≤ C ‖a‖_{W^{-2s+ε,p}(□₀)}`, `λ_{t,1,q}(□₀)⁻¹ ≤ C ‖a⁻¹‖_{W^{-2t+ε,q}(□₀)}`
(e.negative.sobolev.series), and `Θ ≤ C² ‖a‖_{W^{-2s+ε,p}(□₀)} ‖a⁻¹‖_{W^{-2t+ε,q}(□₀)}`.
The binders follow `moment_bounds_besov`; `hA`, `hAinv` (`|a|, |a⁻¹| ∈ L¹(□₀)`, which the
norms presuppose) follow from `ha`. -/
theorem moment_bounds_sobolev (d : ℕ) (_hd : 3 ≤ d) (p q s t ε : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hε : 0 < ε) (hεs : ε ≤ 2 * s) (hεt : ε ≤ 2 * t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
        (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
        (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1))),
        negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA (2 * s - ε) p (sub_nonneg.mpr hεs) hp < ⊤ →
        negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv (2 * t - ε) q
          (sub_nonneg.mpr hεt) hq < ⊤ →
        upperMoment a ha s p hs hp.le ≤
            ENNReal.ofReal C *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA (2 * s - ε) p (sub_nonneg.mpr hεs) hp ∧
          (lowerMoment a ha t q ht hq.le)⁻¹ ≤
            ENNReal.ofReal C *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv (2 * t - ε) q
                (sub_nonneg.mpr hεt) hq ∧
          contrast a ha s t p q hs ht hp.le hq.le ≤
            ENNReal.ofReal (C ^ 2) *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) a hA (2 * s - ε) p (sub_nonneg.mpr hεs) hp *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) (fun x => (a x)⁻¹) hAinv (2 * t - ε) q
                (sub_nonneg.mpr hεt) hq
:=
  by exact CoarseDeGiorgi.NegSobolev.moment_bounds_sobolev_of_negative_sobolev_bound CoarseDeGiorgi.negative_sobolev_bound d _hd p q s t ε hp hq hs ht _hε hεs hεt

end CoarseDeGiorgi
