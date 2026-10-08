import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSolution
import CoarseDeGiorgi.Statements.NonnegativeEssInf

import CoarseDeGiorgi.Endpoint.Chaining.Harnack
import CoarseDeGiorgi.Endpoint.Rescaling.LocalCubes
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `e.interior.harnack`: the interior Harnack estimate for a nonnegative solution in
`(3/4) □₀`; the coefficient field and `Θ` are those of `□₀`. -/
theorem interior_harnack (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube (3 / 4))), 0 ≤ u x) →
          IsWeightedSolution a (originCube (3 / 4)) u G →
          eLpNorm u ⊤ (volume.restrict (originCube (5 / 8))) ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u
:=
  by exact CoarseDeGiorgi.Endpoint.interior_harnack_of_cubes d _hd p q s t hp hq hs ht _hθ (CoarseDeGiorgi.Endpoint.localHarnackCubes_holds d _hd p q s t hp hq hs ht _hθ)

end CoarseDeGiorgi
