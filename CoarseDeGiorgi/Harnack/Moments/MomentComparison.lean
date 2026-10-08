module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Harnack.Moments.ConstantCoefficient
public import CoarseDeGiorgi.Harnack.Moments.DiscountMeans
public import CoarseDeGiorgi.Harnack.Moments.InverseOrder
public import CoarseDeGiorgi.Weighted.LowerResponseSquare
public import CoarseDeGiorgi.Weighted.LowerSpecNorm
public import CoarseDeGiorgi.Weighted.UpperSpecNorm
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem inverse_quadratic_lower_of_upper_bound {d : ℕ} [NeZero d] (M : Mat d)
    (hM : M.PosDef) {L : ℝ} (hL : 0 < L)
    (hbound : ∀ v, vecDot v (matVecMul M v) ≤ L * vecNormSq v) (e : Vec d) :
    L⁻¹ * vecNormSq e ≤ vecDot e (matVecMul (M⁻¹) e) := by
  let g : Vec d := L⁻¹ • e
  have hrem : 0 ≤ vecDot (g - matVecMul M⁻¹ e)
      (matVecMul M (g - matVecMul M⁻¹ e)) := by
    simpa [vecDot, matVecMul, Matrix.mulVec, dotProduct] using
      hM.posSemidef.dotProduct_mulVec_nonneg (g - matVecMul M⁻¹ e)
  have hobjective := Weighted.lower_square_completion M hM e g
  have hobjective_le : -vecDot g (matVecMul M g) + 2 * vecDot e g ≤
      vecDot e (matVecMul M⁻¹ e) := by
    rw [hobjective]
    linarith
  have hqg : vecDot g (matVecMul M g) = L⁻¹ ^ 2 * vecDot e (matVecMul M e) := by
    calc
      _ = L⁻¹ * (L⁻¹ * vecDot e (matVecMul M e)) := by
        simp [g, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
      _ = L⁻¹ ^ 2 * vecDot e (matVecMul M e) := by ring
  have hqg_le : vecDot g (matVecMul M g) ≤ L⁻¹ * vecNormSq e := by
    rw [hqg]
    calc
      L⁻¹ ^ 2 * vecDot e (matVecMul M e) ≤ L⁻¹ ^ 2 * (L * vecNormSq e) :=
        mul_le_mul_of_nonneg_left (hbound e) (sq_nonneg _)
      _ = L⁻¹ * vecNormSq e := by field_simp
  have hdot : vecDot e g = L⁻¹ * vecNormSq e := by
    simp [g, vecDot_smul_right, vecNormSq]
  rw [hdot] at hobjective_le
  nlinarith

/-- The moment comparison `e.moment.comparison`: with `Λ` the upper and `μ` the lower moment,
`Λ⁻¹|e|² ≤ e · a(□)⁻¹ e ≤ e · a_*⁻¹(□) e ≤ μ⁻¹|e|²`, and `μ ≤ Λ`. -/
theorem moment_matrix_sandwich {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {s t p q : ℝ} (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hUpos : 0 < upperMoment a ha s p hs hp)
    (hUfin : upperMoment a ha s p hs hp < ⊤)
    (hLpos : 0 < lowerMoment a ha t q ht hq)
    (hLfin : lowerMoment a ha t q ht hq < ⊤) :
    let Λ := (upperMoment a ha s p hs hp).toReal
    let μ := (lowerMoment a ha t q ht hq).toReal
    (∀ e : Vec d,
      Λ⁻¹ * vecNormSq e ≤
          vecDot e (matVecMul ((upperResponse a (originCube 1)
            LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha)⁻¹) e) ∧
        vecDot e (matVecMul ((upperResponse a (originCube 1)
            LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha)⁻¹) e) ≤
          vecDot e (matVecMul (lowerResponseInv a (originCube 1)
            LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) ∧
        vecDot e (matVecMul (lowerResponseInv a (originCube 1)
            LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha) e) ≤
        μ⁻¹ * vecNormSq e) ∧ μ ≤ Λ := by
  classical
  let U := upperMoment a ha s p hs hp
  let L := lowerMoment a ha t q ht hq
  let Λ : ℝ := U.toReal
  let μ : ℝ := L.toReal
  have hΛ : 0 < Λ := ENNReal.toReal_pos hUpos.ne' hUfin.ne
  have hμ : 0 < μ := ENNReal.toReal_pos hLpos.ne' hLfin.ne
  let A := upperResponse a (originCube 1) LowerFractional.lower_unitCube_domain
    LowerFractional.lower_unitCube_nonempty ha
  let B := lowerResponseInv a (originCube 1) LowerFractional.lower_unitCube_domain
    LowerFractional.lower_unitCube_nonempty ha
  have hAnorm : ‖A‖ ≤ Λ := by
    have h := ENNReal.toReal_mono hUfin.ne (upperMoment_ge_wholeResponse hd a ha hs hp)
    simpa [A, Λ, U, ENNReal.toReal_ofReal (norm_nonneg _)] using h
  have hBnorm : ‖B‖ ≤ μ⁻¹ := by
    have h := ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr hLpos.ne')
      (lowerMoment_inv_ge_wholeResponse hd a ha ht hq)
    simpa [B, μ, L, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_inv] using h
  have hApos : A.PosDef := by
    simpa [A, upperResponse, Weighted.UpperResponseImpl.upperResponse] using
      Weighted.UpperResponseImpl.upperResponse_posDef LowerFractional.lower_unitCube_domain
        LowerFractional.lower_unitCube_nonempty ha
  have hAupper : ∀ e : Vec d, vecDot e (matVecMul A e) ≤ Λ * vecNormSq e := by
    intro e
    calc
      vecDot e (matVecMul A e) ≤ ‖A‖ * vecNormSq e :=
        Weighted.LowerResponseImpl.lower_quadratic_le_norm A e
      _ ≤ Λ * vecNormSq e := mul_le_mul_of_nonneg_right hAnorm (vecNormSq_nonneg e)
  have hsandwich (e : Vec d) :
      Λ⁻¹ * vecNormSq e ≤ vecDot e (matVecMul (A⁻¹) e) ∧
      vecDot e (matVecMul (A⁻¹) e) ≤ vecDot e (matVecMul B e) ∧
      vecDot e (matVecMul B e) ≤ μ⁻¹ * vecNormSq e := by
    refine ⟨@inverse_quadratic_lower_of_upper_bound d ⟨by omega⟩ A hApos Λ hΛ hAupper e,
      ?_, ?_⟩
    · exact inverse_response_order_quadratic hd a ha e
    · calc
        vecDot e (matVecMul B e) ≤ ‖B‖ * vecNormSq e :=
          Weighted.LowerResponseImpl.lower_quadratic_le_norm B e
        _ ≤ μ⁻¹ * vecNormSq e := mul_le_mul_of_nonneg_right hBnorm (vecNormSq_nonneg e)
  have he0 : (basisVec (⟨0, hd⟩ : Fin d) : Vec d) ≠ 0 := by
    intro h
    have hi := congrFun h ⟨0, hd⟩
    simp [basisVec] at hi
  have heNorm : vecNormSq (basisVec (⟨0, hd⟩ : Fin d)) = 1 := by
    classical
    simp only [vecNormSq, vecDot, basisVec, Pi.single_apply]
    rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
    · simp
    · intro i hi hi0
      have hne0 : i ≠ (⟨0, hd⟩ : Fin d) := hi0
      simp [hne0]
    · simp
  have hrecip : Λ⁻¹ ≤ μ⁻¹ := by
    have hs := hsandwich (basisVec (⟨0, hd⟩ : Fin d))
    have hchain := hs.1.trans (hs.2.1.trans hs.2.2)
    calc
      Λ⁻¹ = Λ⁻¹ * vecNormSq (basisVec (⟨0, hd⟩ : Fin d)) := by rw [heNorm]; ring
      _ ≤ μ⁻¹ * vecNormSq (basisVec (⟨0, hd⟩ : Fin d)) := hchain
      _ = μ⁻¹ := by rw [heNorm]; ring
  have hμΛ : μ ≤ Λ := le_of_one_div_le_one_div hΛ (by simpa [one_div] using hrecip)
  refine ⟨?_, hμΛ⟩
  intro e
  simpa [A, B, Λ, μ, U, L] using hsandwich e

private theorem lowerMoment_finite_of_data {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q) :
    lowerMoment a ha t q ht hq < ⊤ := by
  let V := originCube (d := d) 1
  let hV := LowerFractional.lower_unitCube_domain (d := d)
  let hne := LowerFractional.lower_unitCube_nonempty (d := d)
  let B := lowerResponseInv a V hV hne ha
  have hBnorm : 0 < ‖B‖ := by
    simpa [B, lowerResponseInv, Weighted.LowerResponseImpl.lowerResponseInv] using
      Weighted.LowerResponseImpl.lowerResponseInv_norm_pos hV hne ha (by omega)
  have hBinv := lowerMoment_inv_ge_wholeResponse hd a ha ht hq
  have hinvpos : 0 < (lowerMoment a ha t q ht hq)⁻¹ :=
    (ENNReal.ofReal_pos.mpr hBnorm).trans_le hBinv
  have hneTop : lowerMoment a ha t q ht hq ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.inv_top] at hinvpos
    exact (lt_irrefl 0) hinvpos
  exact lt_top_iff_ne_top.mpr hneTop

private theorem upperMoment_pos_of_data {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    0 < upperMoment a ha s p hs hp := by
  let V := originCube (d := d) 1
  let hV := LowerFractional.lower_unitCube_domain (d := d)
  let hne := LowerFractional.lower_unitCube_nonempty (d := d)
  let A := upperResponse a V hV hne ha
  have hAnorm : 0 < ‖A‖ := by
    simpa [A, upperResponse, Weighted.UpperResponseImpl.upperResponse] using
      Weighted.UpperResponseImpl.upperResponse_norm_pos hV hne ha (by omega)
  have hwhole := upperMoment_ge_wholeResponse hd a ha hs hp
  exact (ENNReal.ofReal_pos.mpr hAnorm).trans_le hwhole

/-- The contrast is at least one. -/
theorem moment_contrast_ge_one {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {s t p q : ℝ} (hs : 0 < s) (ht : 0 < t) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hUfin : upperMoment a ha s p hs hp < ⊤)
    (hLpos : 0 < lowerMoment a ha t q ht hq) :
    1 ≤ contrast a ha s t p q hs ht hp hq := by
  have hUpos : 0 < upperMoment a ha s p hs hp := upperMoment_pos_of_data hd a ha hs hp
  have hLfin : lowerMoment a ha t q ht hq < ⊤ := lowerMoment_finite_of_data hd a ha ht hq
  have hcomp := moment_matrix_sandwich hd a ha hs ht hp hq hUpos hUfin hLpos hLfin
  have hLleU : lowerMoment a ha t q ht hq ≤ upperMoment a ha s p hs hp :=
    (ENNReal.toReal_le_toReal hLfin.ne hUfin.ne).mp hcomp.2
  rw [contrast]
  exact (ENNReal.le_div_iff_mul_le (Or.inl hLpos.ne') (Or.inl hLfin.ne)).2 (by simpa using hLleU)

end CoarseDeGiorgi.Harnack.Moments
