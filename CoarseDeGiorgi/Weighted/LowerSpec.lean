module

public import CoarseDeGiorgi.Weighted.LowerSpecNorm

@[expose] public section

namespace CoarseDeGiorgi.Weighted.LowerResponseImpl

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- The full supremum, mean-gradient, and coefficient-bound characterization of the lower response. -/
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
      ‖B‖ ≤ ‖volumeAverageMat V (fun x => (a x)⁻¹)‖ := by
  dsimp only
  refine ⟨lowerResponseInv_posDef hV hV₀ ha,
    (fun M hM he => lowerResponseInv_unique hV hV₀ ha M hM he),
    lowerResponseInv_directional hV hV₀ ha,
    lowerResponseInv_all_functions hV hV₀ ha,
    lowerResponseInv_attained hV hV₀ ha, ?_,
    lowerResponseInv_coefficient_bound hV hV₀ ha,
    lowerResponseInv_norm_pos hV hV₀ ha, lowerResponseInv_norm_le hV hV₀ ha⟩
  intro w G hw
  exact ⟨lowerResponseInv_mean_gradient hV hV₀ ha hw,
    lowerResponseInv_mean_gradient_norm hV hV₀ ha hw⟩


end CoarseDeGiorgi.Weighted.LowerResponseImpl
