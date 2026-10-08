module

public import CoarseDeGiorgi.Weighted.UpperSpecMinimum
public import CoarseDeGiorgi.Weighted.UpperSpecNorm

@[expose] public section

namespace CoarseDeGiorgi.Weighted.UpperResponseImpl

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- The full affine-boundary characterization and coefficient domination for the upper response. -/
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
      ‖A‖ ≤ ‖volumeAverageMat V a‖ := by
  refine ⟨upperResponse_posDef hV hV₀ ha,
    fun M hM he => upperResponse_unique hV hV₀ ha M hM he,
    upperResponse_directional hV hV₀ ha,
    upper_affine_replacement hV hV₀ ha,
    fun e c h Gh hh hb => upper_affine_energy hV hV₀ ha e c hh hb,
    upper_affine_minimum hV hV₀ ha,
    upper_coefficient_bound hV.isOpen ha,
    upperResponse_norm_pos hV hV₀ ha,
    upperResponse_norm_le hV hV₀ ha⟩


end CoarseDeGiorgi.Weighted.UpperResponseImpl
