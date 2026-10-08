module

public import Homogenization.Ambient.CoefficientField
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import CoarseDeGiorgi.Statements.MemH1a
public import CoarseDeGiorgi.Statements.MemH1a0
public import CoarseDeGiorgi.Statements.UpperDirectionalResponseSol
public import CoarseDeGiorgi.Statements.UpperDirectionalResponseSub
public import CoarseDeGiorgi.Statements.UpperResponse
public import CoarseDeGiorgi.Weighted.UpperSpec

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem upperResponse_spec {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    let A := upperResponse a V hV hV₀ ha
    A.PosDef ∧
    (∀ A' : Mat d, A'.PosDef →
      (∀ e : Vec d, ((vecDot e (matVecMul A' e) : ℝ) : EReal) =
        upperDirectionalResponseSol a V e) → A' = A) ∧
    (∀ e : Vec d, ((vecDot e (matVecMul A e) : ℝ) : EReal) =
      upperDirectionalResponseSol a V e) ∧
    (∀ e : Vec d, ∀ c : ℝ, ∃ h : Vec d → ℝ, ∃ Gh : Vec d → Vec d,
      IsWeightedSolution a V h Gh ∧
      MemH1a0 a V (fun x => h x - (vecDot e x + c))
        (fun x => Gh x - e)) ∧
    (∀ e : Vec d, ∀ c : ℝ, ∀ h : Vec d → ℝ, ∀ Gh : Vec d → Vec d,
      IsWeightedSolution a V h Gh →
      MemH1a0 a V (fun x => h x - (vecDot e x + c))
        (fun x => Gh x - e) →
      (vecDot e (matVecMul A e) : ℝ) =
        volumeAverage V (fun x => vecDot (Gh x) (matVecMul (a x) (Gh x)))) ∧
    (∀ e : Vec d,
      IsLeast
        {v : ℝ | ∃ h : Vec d → ℝ, ∃ Gh : Vec d → Vec d,
          MemH1a a V h Gh ∧
          MemH1a0 a V (fun x => h x - vecDot e x)
            (fun x => Gh x - e) ∧
          v = volumeAverage V
            (fun x => vecDot (Gh x) (matVecMul (a x) (Gh x)))}
        (vecDot e (matVecMul A e))) ∧
    (∀ e : Vec d,
      0 ≤ upperDirectionalResponseSol a V e ∧
      upperDirectionalResponseSol a V e ≤ upperDirectionalResponseSub a V e ∧
      upperDirectionalResponseSub a V e ≤
        ((vecDot e (matVecMul (volumeAverageMat V a) e) : ℝ) : EReal)) ∧
    (0 < d → 0 < ‖A‖) ∧
      ‖A‖ ≤ ‖volumeAverageMat V a‖ :=
  CoarseDeGiorgi.Weighted.UpperResponseImpl.upperResponse_spec hV hV₀ ha

end CoarseDeGiorgi
