module

public import CoarseDeGiorgi.Weighted.UpperSpecDefs
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Matrix.Hermitian

@[expose] public section

namespace CoarseDeGiorgi.Weighted.UpperResponseImpl

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator

/-- Quadratic domination of a positive matrix implies domination of its ℓ² operator norm. -/
theorem matrix_l2_norm_le_of_quadratic {d : ℕ} {A B : Mat d} (hA : A.PosSemidef)
    (hle : ∀ e : Vec d, vecDot e (matVecMul A e) ≤ vecDot e (matVecMul B e)) :
    ‖A‖ ≤ ‖B‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A
  let S := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) B
  have hs : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.isHermitian
  have inner_eq (M : Mat d) (x : EuclideanSpace ℝ (Fin d)) :
      inner ℝ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M x) x = vecDot x (matVecMul M x) := by
    simp [PiLp.inner_apply, Matrix.ofLp_toEuclideanCLM, vecDot, matVecMul, Matrix.mulVec,
      dotProduct]
  change ‖T‖ ≤ ‖S‖
  rw [T.norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro x
  have hp : 0 ≤ vecDot x (matVecMul A x) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      hA.dotProduct_mulVec_nonneg (x := x.ofLp)
  have ht : T.rayleighQuotient x = vecDot x (matVecMul A x) / ‖x‖ ^ 2 := by
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real, T, inner_eq]
  have hs' : S.rayleighQuotient x = vecDot x (matVecMul B x) / ‖x‖ ^ 2 := by
    simp only [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real, S, inner_eq]
  rw [ht, abs_of_nonneg (div_nonneg hp (sq_nonneg _))]
  calc
    _ ≤ vecDot x (matVecMul B x) / ‖x‖ ^ 2 :=
      div_le_div_of_nonneg_right (hle x.ofLp) (sq_nonneg _)
    _ = S.rayleighQuotient x := hs'.symm
    _ ≤ |S.rayleighQuotient x| := le_abs_self _
    _ ≤ ‖S‖ := S.rayleighQuotient_le_norm x

/-- The full coefficient chain supplies the matrix's ℓ² operator norm bound. -/
theorem upperResponse_norm_le {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    ‖upperResponse a V hV hne ha‖ ≤ ‖volumeAverageMat V a‖ := by
  apply matrix_l2_norm_le_of_quadratic (upperResponse_posDef hV hne ha).posSemidef
  intro e
  apply EReal.coe_le_coe_iff.mp
  rw [upperResponse_directional hV hne ha e]
  exact (upper_coefficient_bound hV.isOpen ha e).2.1.trans
    (upper_coefficient_bound hV.isOpen ha e).2.2

/-- Positive definite matrices have strictly positive norm in positive dimension. -/
theorem upperResponse_norm_pos {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (hd : 0 < d) :
    0 < ‖upperResponse a V hV hne ha‖ := by
  apply norm_pos_iff.mpr
  intro hz
  let i : Fin d := ⟨0, hd⟩
  have he : basisVec i ≠ 0 := by
    intro h
    have hi := congrFun h i
    simp [basisVec] at hi
  have hp := (upperResponse_posDef hV hne ha).dotProduct_mulVec_pos he
  rw [hz] at hp
  simp at hp


end CoarseDeGiorgi.Weighted.UpperResponseImpl
