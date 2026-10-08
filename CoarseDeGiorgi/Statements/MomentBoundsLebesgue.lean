import Homogenization.Ambient.CoefficientField
import Homogenization.CoarseGraining.Definitions
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.UpperMoment

import CoarseDeGiorgi.CoefficientConditions.Lebesgue
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem moment_bounds_lebesgue (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (_hap : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (originCube 1)) < ⊤)
    (_haq : eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q)
      (volume.restrict (originCube 1)) < ⊤) :
    upperMoment a ha s p hs hp.le ≤
        eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) ∧
      (lowerMoment a ha t q ht hq.le)⁻¹ ≤
        eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) (volume.restrict (originCube 1)) ∧
      contrast a ha s t p q hs ht hp.le hq.le ≤
        eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) *
          eLpNorm (fun x => ‖(a x)⁻¹‖) (ENNReal.ofReal q) (volume.restrict (originCube 1))
:=
  CoarseDeGiorgi.CoefficientConditions.moment_bounds_lebesgue_aux hp hq hs ht a ha _hap _haq

end CoarseDeGiorgi
