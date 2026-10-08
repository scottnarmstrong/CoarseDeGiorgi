module

public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.MemH1a0
public import CoarseDeGiorgi.Statements.LowerMoment
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.RStarParam
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.SmoothGrad

public import CoarseDeGiorgi.Endpoint.Potential.Main
public import CoarseDeGiorgi.Statements.DirichletReconstruction

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.endpoint.potential`: the endpoint estimate for potentials of measures.
`v` is the potential of `ν` (`v ∈ H¹_{a,0}(□₀)`, `∫ ∇φ·a∇v = ∫ φ dν`), tested on `C_c^∞(□₀)`. -/
theorem endpoint_potential (d : ℕ) (_hd : 3 ≤ d) (q t : ℝ) (hq : 1 < q) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (p s : ℝ) (hp : 1 < p) (hs : 0 < s),
        0 < paramTheta d p q s t →
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (ν : Measure (Vec d)), IsFiniteMeasure ν → ν (originCube 1)ᶜ = 0 →
          (∃ M : ℝ, 0 ≤ M ∧
            ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
              tsupport φ ⊆ originCube 1 →
              ENNReal.ofReal |∫ x, φ x ∂ν| ≤
                ENNReal.ofReal M *
                  (weightedEnergy a (originCube 1) (smoothGrad φ)).rpow (1 / 2)) →
        ∀ (v : Vec d → ℝ) (Gv : Vec d → Vec d),
          MemH1a0 a (originCube 1) v Gv →
          (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
              tsupport φ ⊆ originCube 1 →
              ∫ x in originCube 1, vecDot (smoothGrad φ x) (matVecMul (a x) (Gv x)) ∂volume =
                ∫ x, φ x ∂ν) →
          eLpNorm v (ENNReal.ofReal (rStarParam (d := d) q t / 2))
              (volume.restrict (originCube 1)) ≤
            ENNReal.ofReal C * (lowerMoment a ha t q ht hq.le)⁻¹ * ν (originCube 1)
:=
  by exact CoarseDeGiorgi.Endpoint.endpoint_potential_of_reconstruction d _hd q t hq ht (CoarseDeGiorgi.dirichlet_reconstruction d _hd q hq)

end CoarseDeGiorgi
