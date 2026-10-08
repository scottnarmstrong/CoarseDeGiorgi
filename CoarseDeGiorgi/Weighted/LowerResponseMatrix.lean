import CoarseDeGiorgi.Weighted.LowerResponseHilbert

/-! Finite matrix representation of the Riesz energy and uniqueness by polarization. -/

namespace CoarseDeGiorgi.Weighted

open Homogenization
open scoped BigOperators

variable {d : ℕ}

/-- Coordinate vectors give the usual finite expansion. -/
theorem lower_basis_sum (e : Vec d) : (∑ i : Fin d, e i • basisVec i) = e := by
  classical
  funext j
  simp [basisVec, Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

/-- Gram matrix of a linear map, multiplied by a scalar normalization. -/
noncomputable def lowerGramMatrix {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : Vec d →ₗ[ℝ] H) (c : ℝ) : Mat d :=
  fun i j => c * inner ℝ (T (basisVec i)) (T (basisVec j))

/-- The Gram matrix represents the squared Hilbert norm. -/
theorem lowerGramMatrix_quadratic {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : Vec d →ₗ[ℝ] H) (c : ℝ) (e : Vec d) :
    vecDot e (matVecMul (lowerGramMatrix T c) e) = c * ‖T e‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← lower_basis_sum e]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right]
  rw [lower_basis_sum e]
  simp only [vecDot, matVecMul, lowerGramMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (T (basisVec i)) (T (basisVec j))]
  ring

/-- A positive scalar Gram matrix is positive definite for an injective map. -/
theorem lowerGramMatrix_posDef {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : Vec d →ₗ[ℝ] H) {c : ℝ} (hc : 0 < c)
    (hT : Function.Injective T) : (lowerGramMatrix T c).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun e he => ?_⟩
  · simp only [lowerGramMatrix, star_trivial]
    rw [real_inner_comm]
  · have hTe : T e ≠ 0 := fun hz => he (hT (hz.trans T.map_zero.symm))
    have hn : 0 < ‖T e‖ ^ 2 := pow_pos (norm_pos_iff.mpr hTe) 2
    have hh := lowerGramMatrix_quadratic T c e
    have hp := mul_pos hc hn
    rw [← hh] at hp
    simpa only [star_trivial, dotProduct, Matrix.mulVec, vecDot, matVecMul] using hp

/-- Symmetric real matrices are determined by their quadratic forms. -/
theorem lower_matrix_ext {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef)
    (h : ∀ e, vecDot e (matVecMul A e) = vecDot e (matVecMul B e)) : A = B := by
  classical
  have hAs : A.IsSymm := by simpa [Matrix.IsSymm, Matrix.IsHermitian] using hA.1
  have hBs : B.IsSymm := by simpa [Matrix.IsSymm, Matrix.IsHermitian] using hB.1
  have hc (e f : Vec d) : vecDot f (matVecMul A e) = vecDot f (matVecMul B e) := by
    rw [← half_vecDot_sub_polarization_of_isSymm hAs,
      ← half_vecDot_sub_polarization_of_isSymm hBs, h e, h f, h (e - f)]
  ext i j
  have hh := hc (basisVec j) (basisVec i)
  rw [vecDot_basisVec_left, vecDot_basisVec_left] at hh
  simpa only [basisVec, matVecMul_single] using hh


end CoarseDeGiorgi.Weighted
