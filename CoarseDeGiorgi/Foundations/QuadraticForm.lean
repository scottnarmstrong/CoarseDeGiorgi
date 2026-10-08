import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace CoarseDeGiorgi.Foundations

open Homogenization

variable {d : ℕ}

/-- The squared Euclidean norm is controlled by the inverse trace times the
positive quadratic form. -/
theorem vecDot_self_le_inv_trace_mul_quadratic
    (A : Mat d) (hA : A.PosDef) (ξ : Vec d) :
    vecDot ξ ξ ≤ (A⁻¹).trace * vecDot ξ (matVecMul A ξ) := by
  classical
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det (A := A)).mp hA.isUnit
  have hsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.1
  have hterm (i : Fin d) :
      ξ i ^ 2 ≤ (A⁻¹) i i * vecDot ξ (matVecMul A ξ) := by
    let e : Vec d := basisVec i
    let x : Vec d := matVecMul A⁻¹ e
    have hAx : matVecMul A x = e := by
      dsimp [x]
      rw [matVecMul_mul, Matrix.mul_nonsing_inv A hdet]
      funext j
      simp [matVecMul, e, Matrix.one_apply]
    have hcross : vecDot x (matVecMul A ξ) = ξ i := by
      calc
        vecDot x (matVecMul A ξ) = vecDot ξ (matVecMul A x) :=
          vecDot_matVecMul_comm_of_isSymm hsymm x ξ
        _ = vecDot ξ e := by rw [hAx]
        _ = ξ i := by
          exact vecDot_basisVec_right ξ i
    have hxx : vecDot x (matVecMul A x) = (A⁻¹) i i := by
      rw [hAx]
      dsimp [x, e]
      rw [vecDot_basisVec_right]
      change (matVecMul A⁻¹ (Pi.single i 1)) i = (A⁻¹) i i
      rw [matVecMul_single]
    have hcs := hA.star_dotProduct_mulVec_mul_le x ξ
    have hcs' : (vecDot x (matVecMul A ξ)) ^ 2 ≤
        vecDot x (matVecMul A x) * vecDot ξ (matVecMul A ξ) := by
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul, pow_two] using hcs
    rw [hcross, hxx] at hcs'
    exact hcs'
  calc
    vecDot ξ ξ = ∑ i : Fin d, ξ i ^ 2 := by simp [vecDot, pow_two]
    _ ≤ ∑ i : Fin d, (A⁻¹) i i * vecDot ξ (matVecMul A ξ) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i : Fin d, (A⁻¹) i i) * vecDot ξ (matVecMul A ξ) := by
      rw [Finset.sum_mul]
    _ = (A⁻¹).trace * vecDot ξ (matVecMul A ξ) := by
      simp [Matrix.trace]

/-- The squared Euclidean norm of the image is controlled by the trace times
the positive quadratic form. -/
theorem vecDot_matVecMul_self_le_trace_mul_quadratic
    (A : Mat d) (hA : A.PosDef) (ξ : Vec d) :
    vecDot (matVecMul A ξ) (matVecMul A ξ) ≤
      A.trace * vecDot ξ (matVecMul A ξ) := by
  classical
  have hterm (i : Fin d) :
      (matVecMul A ξ i) ^ 2 ≤ A i i * vecDot ξ (matVecMul A ξ) := by
    let e : Vec d := basisVec i
    have hcross : vecDot e (matVecMul A ξ) = matVecMul A ξ i := by
      exact vecDot_basisVec_left i _
    have hee : vecDot e (matVecMul A e) = A i i := by
      calc
        vecDot e (matVecMul A e) = (matVecMul A e) i := by
          exact vecDot_basisVec_left i _
        _ = A i i := by
          change (matVecMul A (Pi.single i 1)) i = A i i
          rw [matVecMul_single]
    have hcs := hA.star_dotProduct_mulVec_mul_le e ξ
    have hcs' : (vecDot e (matVecMul A ξ)) ^ 2 ≤
        vecDot e (matVecMul A e) * vecDot ξ (matVecMul A ξ) := by
      simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul, pow_two] using hcs
    rw [hcross, hee] at hcs'
    exact hcs'
  calc
    vecDot (matVecMul A ξ) (matVecMul A ξ) =
        ∑ i : Fin d, (matVecMul A ξ i) ^ 2 := by simp [vecDot, pow_two]
    _ ≤ ∑ i : Fin d, A i i * vecDot ξ (matVecMul A ξ) :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i : Fin d, A i i) * vecDot ξ (matVecMul A ξ) := by
      rw [Finset.sum_mul]
    _ = A.trace * vecDot ξ (matVecMul A ξ) := by
      simp [Matrix.trace]

end CoarseDeGiorgi.Foundations
