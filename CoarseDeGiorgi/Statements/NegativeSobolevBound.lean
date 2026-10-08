import Homogenization.Ambient.CoefficientField
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.BesovCubeNorm
import CoarseDeGiorgi.Statements.NegSobolevNorm
import CoarseDeGiorgi.Statements.IsOpenOriginCube

import CoarseDeGiorgi.NegSobolev.LemmaB2Assembly
import CoarseDeGiorgi.NegSobolev.TestNormGaussian
import CoarseDeGiorgi.Statements.BesovAverages
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Lemma `l.negative.sobolev`, finite `1 < p < ∞`: for `s > 0`
and `0 < ε ≤ 2s` there is `C = C(d, p, s, ε)` such that every matrix field `b` on `□₀`,
symmetric and positive semidefinite a.e. with `|b| ∈ L¹(□₀)`, satisfies
`‖b‖_{B̊^{-2s}_{p,1/2}(□₀)} ≤ C ‖b‖_{W^{-2s+ε,p}(□₀)}`, with the quasi-norm
`e.negative.regularity.norm` (`besovCubeNorm`) and the negative Sobolev norm
(e.negative.sobolev.norm) of order `-(2s - ε)` (`negSobolevNorm` with `β = 2s - ε ≥ 0`). -/
theorem negative_sobolev_bound (d : ℕ) (p s ε : ℝ)
    (hp : 1 < p) (hs : 0 < s) (_hε : 0 < ε) (hεs : ε ≤ 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Vec d → Mat d),
        (∀ᵐ x ∂(volume.restrict (originCube 1)), (b x).PosSemidef) →
        ∀ (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1))),
          besovCubeNorm b hb s p hs hp.le ≤
            ENNReal.ofReal C *
              negSobolevNorm (originCube 1) (isOpen_originCube 1) b hb (2 * s - ε) p (sub_nonneg.mpr hεs) hp
:=
  by exact CoarseDeGiorgi.NegSobolev.negative_sobolev_bound_of_inputs CoarseDeGiorgi.besov_averages CoarseDeGiorgi.NegSobolev.gaussian_test_sobolev_bound d p s ε hp hs _hε hεs

end CoarseDeGiorgi
