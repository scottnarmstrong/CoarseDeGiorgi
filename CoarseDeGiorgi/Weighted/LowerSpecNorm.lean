module

public import CoarseDeGiorgi.Weighted.LowerSpecMean
public import CoarseDeGiorgi.Weighted.UpperSpecNorm

@[expose] public section

namespace CoarseDeGiorgi.Weighted.LowerResponseImpl

open Homogenization MeasureTheory
open scoped Matrix.Norms.L2Operator

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The Euclidean operator norm bounds the real quadratic form. -/
theorem lower_quadratic_le_norm (M : Mat d) (e : Vec d) :
    vecDot e (matVecMul M e) ≤ ‖M‖ * vecNormSq e := by
  let x : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 e
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (matVecMul M e)
  have hi : inner ℝ x y = vecDot e (matVecMul M e) := by
    simp only [x, y, EuclideanSpace.inner_toLp_toLp, star_trivial, vecDot, matVecMul,
      dotProduct, mul_comm]
  have hn : ‖x‖ ^ 2 = vecNormSq e := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [x, vecNormSq, vecDot, sq]
  have hy : ‖y‖ ≤ ‖M‖ * ‖x‖ := Matrix.l2_opNorm_mulVec M x
  calc
    _ = inner ℝ x y := hi.symm
    _ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖M‖ * ‖x‖) := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = ‖M‖ * vecNormSq e := by rw [← hn]; ring

/-- Source e.lower.mean.gradient, its Euclidean squared-length consequence. -/
theorem lowerResponseInv_mean_gradient_norm
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) :
    vecNormSq (volumeAverageVec V G) ≤
      ‖lowerResponseInv a V hV hne ha‖ *
        volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x))) := by
  let v := volumeAverageVec V G
  have hE : 0 ≤ volumeAverage V (fun x => vecDot (G x) (matVecMul (a x) (G x))) := by
    unfold volumeAverage
    apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    apply integral_nonneg_of_ae
    filter_upwards [ha.2.1] with x hx
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using hx.posSemidef.dotProduct_mulVec_nonneg (G x)
  have hd := lowerResponseInv_mean_gradient hV hne ha hw v
  have hn := mul_le_mul_of_nonneg_right
    (lower_quadratic_le_norm (lowerResponseInv a V hV hne ha) v) hE
  change vecNormSq v ^ 2 ≤ _ at hd
  have hv := vecNormSq_nonneg v
  rcases hv.eq_or_lt with hz | hp
  · rw [← hz]
    exact mul_nonneg (norm_nonneg _) hE
  · nlinarith [hd.trans hn]

/-- The shared directional coefficient bound transported to the matrix `lowerResponseInv`. -/
theorem lowerResponseInv_coefficient_bound
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    vecDot e (matVecMul (lowerResponseInv a V hV hne ha) e) ≤
      volumeAverage V (fun x => vecDot e (matVecMul ((a x)⁻¹) e)) := by
  apply EReal.coe_le_coe_iff.mp
  rw [lowerResponseInv_directional, response_quadratic_average (response_inverse_coefficient ha)]
  exact lower_coefficient_bound hV.isOpen ha e

/-- Quadratic domination gives domination of the L² operator norms. -/
theorem lowerResponseInv_norm_le
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) :
    ‖lowerResponseInv a V hV hne ha‖ ≤
      ‖volumeAverageMat V (fun x => (a x)⁻¹)‖ := by
  apply UpperResponseImpl.matrix_l2_norm_le_of_quadratic
    (lowerResponseInv_posDef hV hne ha).posSemidef
  intro e
  rw [← response_quadratic_average (response_inverse_coefficient ha)]
  exact lowerResponseInv_coefficient_bound hV hne ha e

/-- In a positive dimension the positive definite response has nonzero norm. -/
theorem lowerResponseInv_norm_pos
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (hd : 0 < d) :
    0 < ‖lowerResponseInv a V hV hne ha‖ := by
  apply norm_pos_iff.mpr
  intro hz
  let i : Fin d := ⟨0, hd⟩
  have he : (basisVec i : Vec d) ≠ 0 := by
    intro h
    have := congrFun h i
    simp [basisVec] at this
  have hp := (lowerResponseInv_posDef hV hne ha).dotProduct_mulVec_pos he
  rw [hz] at hp
  simp at hp


end CoarseDeGiorgi.Weighted.LowerResponseImpl
