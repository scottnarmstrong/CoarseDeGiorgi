import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.UpperResponse
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn

import CoarseDeGiorgi.Cubical.UpperMain
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- `e.upper.subadditivity`, countable form, for open bounded convex domains. -/
theorem upper_subadditivity_countable
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hU₀ : U.Nonempty) (ha : IsWeightedCoeffOn U a)
    {ι : Type} [Countable ι] (V : ι → Set (Vec d))
    (hV : ∀ i, IsOpenBoundedConvexDomain (V i)) (hV₀ : ∀ i, (V i).Nonempty)
    (haV : ∀ i, IsWeightedCoeffOn (V i) a)
    (hVU : ∀ i, V i ⊆ U) (hdisj : Pairwise (Function.onFun Disjoint V))
    (hcover : volume (U \ ⋃ i, V i) = 0) :
    Summable (fun i => ‖(((volume (V i)).toReal / (volume U).toReal : ℝ)) •
        upperResponse a (V i) (hV i) (hV₀ i) (haV i)‖) ∧
    (∑' i, (((volume (V i)).toReal / (volume U).toReal : ℝ)) •
        upperResponse a (V i) (hV i) (hV₀ i) (haV i) -
      upperResponse a U hU hU₀ ha).PosSemidef
:=
  CoarseDeGiorgi.Cubical.upper_subadditivity_countable_main hU hU₀ ha V hV hV₀ haV hVU hdisj hcover

end CoarseDeGiorgi
