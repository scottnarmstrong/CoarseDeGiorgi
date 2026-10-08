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
public import CoarseDeGiorgi.Statements.LowerDirectionalResponse
public import CoarseDeGiorgi.Statements.LowerResponseInv
public import CoarseDeGiorgi.Weighted.LowerSpec

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem lowerResponseInv_spec {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    let B := lowerResponseInv a V hV hV₀ ha
    B.PosDef ∧
    (∀ A' : Mat d, A'.PosDef →
      (∀ e : Vec d, ((vecDot e (matVecMul A' e) : ℝ) : EReal) =
        lowerDirectionalResponse a V e) → A' = B) ∧
    (∀ e : Vec d, ((vecDot e (matVecMul B e) : ℝ) : EReal) =
      lowerDirectionalResponse a V e) ∧
    (∀ e : Vec d,
      ((vecDot e (matVecMul B e) : ℝ) : EReal) =
        ⨆ (w : Vec d → ℝ) (G : Vec d → Vec d) (_ : MemH1a a V w G),
          ((volumeAverage V
            (fun x => -vecDot (G x) (matVecMul (a x) (G x)) + 2 * vecDot e (G x)) : ℝ) : EReal)) ∧
    (∀ e : Vec d, ∃ w : Vec d → ℝ, ∃ G : Vec d → Vec d,
      IsWeightedSolution a V w G ∧ IntegrableOn w V ∧ volumeAverage V w = 0 ∧
      ((volumeAverage V
        (fun x => -vecDot (G x) (matVecMul (a x) (G x)) + 2 * vecDot e (G x)) : ℝ) : EReal) =
          ((vecDot e (matVecMul B e) : ℝ) : EReal)) ∧
    (∀ w : Vec d → ℝ, ∀ G : Vec d → Vec d, MemH1a a V w G →
      (∀ e : Vec d,
        (vecDot e (volumeAverageVec V G)) ^ 2 ≤
          vecDot e (matVecMul B e) *
            volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x)))) ∧
        vecNormSq (volumeAverageVec V G) ≤
          ‖B‖ * volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x)))) ∧
    (∀ e : Vec d,
      vecDot e (matVecMul B e) ≤
        volumeAverage V (fun x => vecDot e (matVecMul ((a x)⁻¹) e))) ∧
    (0 < d → 0 < ‖B‖) ∧
      ‖B‖ ≤ ‖volumeAverageMat V (fun x => (a x)⁻¹)‖ :=
  CoarseDeGiorgi.Weighted.LowerResponseImpl.lowerResponseInv_spec hV hV₀ ha

end CoarseDeGiorgi
