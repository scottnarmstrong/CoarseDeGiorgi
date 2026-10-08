module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Data.EReal.Basic
public import CoarseDeGiorgi.Weighted.UpperResponse

@[expose] public section

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
