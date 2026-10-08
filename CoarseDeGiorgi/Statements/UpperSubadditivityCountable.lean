module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.UpperResponse
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn

public import CoarseDeGiorgi.Cubical.UpperMain

@[expose] public section

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
