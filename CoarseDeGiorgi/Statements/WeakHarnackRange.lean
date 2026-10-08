import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.NormalizedLpMoment
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.RStarParam

import CoarseDeGiorgi.Endpoint.Completion.Main
import CoarseDeGiorgi.Statements.EndpointPotential
import CoarseDeGiorgi.Statements.SourceMassPotential
import CoarseDeGiorgi.Statements.InteriorHarnack
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem weak_harnack_range (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∀ (η : ℝ) (hη : 0 < η), η ≤ rStarParam (d := d) q t / 2 →
    ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment η hη (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u
:=
  by exact CoarseDeGiorgi.Endpoint.weak_harnack_range_of_endpoint d _hd p q s t hp hq hs ht _hθ (CoarseDeGiorgi.endpoint_potential d _hd q t hq ht) (CoarseDeGiorgi.source_mass_potential d _hd p q s t hp hq hs ht _hθ) (CoarseDeGiorgi.interior_harnack d _hd p q s t hp hq hs ht _hθ)

end CoarseDeGiorgi
