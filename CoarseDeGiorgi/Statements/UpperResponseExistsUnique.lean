import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Data.EReal.Basic
import CoarseDeGiorgi.Weighted.UpperResponse

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

theorem upperResponse_existsUnique {d : ℕ} {V : Set (Vec d)}
    {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    ∃! A : Mat d, A.PosDef ∧
      ∀ e : Vec d,
        ((vecDot e (matVecMul A e) : ℝ) : EReal) =
          upperDirectionalResponseSol a V e :=
  CoarseDeGiorgi.Weighted.upperResponse_existsUnique_proved hV hV₀ ha

end CoarseDeGiorgi
