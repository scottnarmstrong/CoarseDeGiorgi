module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.IsWeightedSupersolution
public import CoarseDeGiorgi.Statements.NonnegativeEssInf
public import CoarseDeGiorgi.Statements.HarnackEtaParam

public import CoarseDeGiorgi.Endpoint.Chaining.WeakHarnack
public import CoarseDeGiorgi.Endpoint.Rescaling.LocalCubes

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `e.interior.weak.harnack`: the interior weak Harnack estimate at `η = r/4`
on `(15/16) □₀`. -/
theorem interior_weak_harnack (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          eLpNorm u (ENNReal.ofReal (harnackEtaParam q))
              (volume.restrict (originCube (15 / 16))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (15 / 16)) u
:=
  by exact CoarseDeGiorgi.Endpoint.interior_weak_harnack_of_cubes d _hd p q s t hp hq hs ht _hθ (CoarseDeGiorgi.Endpoint.localWeakHarnackCubes_holds d _hd p q s t hp hq hs ht _hθ)

end CoarseDeGiorgi
