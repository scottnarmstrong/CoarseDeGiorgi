import CoarseDeGiorgi.Weighted.LowerResponseSquare
import CoarseDeGiorgi.Weighted.LowerResponseMatrix
import CoarseDeGiorgi.Weighted.UpperResponseAffine

/-! Existence and uniqueness of the lower-response matrix. -/

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- The gradient component of the directional Riesz map. -/
noncomputable def lowerResponseGradient (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) :
    Vec d →ₗ[ℝ] GradientHilbert ha :=
  ((WithLp.sndL 2 ℝ ℝ (GradientHilbert ha)).comp
    (weightedSubmodule hV ha).subtypeL).toLinearMap.comp (lowerRieszLinear hV ha)


/-- Affine tests make the Riesz gradient map injective. -/
theorem lowerResponseGradient_injective [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) :
    Function.Injective (lowerResponseGradient hV.isOpen ha) := by
  have hvol : (volume V).toReal ≠ 0 :=
    (ENNReal.toReal_pos (hV.isOpen.measure_pos volume hne).ne'
      hV.isBoundedDomain.isBounded.measure_lt_top.ne).ne'
  have hz (e : Vec d) (he : lowerResponseGradient hV.isOpen ha e = 0) : e = 0 := by
    have hh := lowerRiesz_pair hV hne ha e (responseAffine_memH1a hV ha e)
    change (lowerRiesz hV.isOpen ha e).val.snd = 0 at he
    rw [he, inner_zero_right] at hh
    have hq : vecDot e e = 0 := by
      have hi : (volume V).toReal * vecDot e e = 0 := by
        simpa only [setIntegral_const, smul_eq_mul, measureReal_def] using hh.symm
      exact (mul_eq_zero.mp hi).resolve_left hvol
    exact vecNormSq_eq_zero hq
  intro e f hef
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hef, sub_self]

/-- Square completion and harmonic attainment identify the extended supremum. -/
theorem lowerDirectionalResponse_eq_riesz [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    lowerDirectionalResponse a V e =
      (((volume V).toReal⁻¹ * ‖lowerResponseGradient hV.isOpen ha e‖ ^ 2 : ℝ) : EReal) := by
  apply le_antisymm
  · unfold lowerDirectionalResponse
    refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
    exact EReal.coe_le_coe (lower_integrand_le hV hne ha e hw.1)
  · obtain ⟨u, hu, _⟩ := exists_lowerRiesz_solution hV hne ha e
    let U := gradientHilbertRep ha (lowerRiesz hV.isOpen ha e).val.snd
    have hU : (memH1aEnergyField hV.isOpen ha hu.1 : GradientHilbert ha) =
        (lowerRiesz hV.isOpen ha e).val.snd := by
      calc
        (memH1aEnergyField hV.isOpen ha hu.1 : GradientHilbert ha) =
            (U : GradientHilbert ha) := by
          apply (GradientCore.coe_eq_iff ha _ _).mpr
          exact Filter.EventuallyEq.rfl
        _ = (lowerRiesz hV.isOpen ha e).val.snd := gradientHilbertRep_coe ha _
    have he : volumeAverage V (fun x =>
        -vecDot (U.field x) (matVecMul (a x) (U.field x)) + 2 * vecDot e (U.field x)) =
        (volume V).toReal⁻¹ * ‖lowerResponseGradient hV.isOpen ha e‖ ^ 2 := by
      rw [lower_integrand_eq hV hne ha e hu.1, hU, sub_self, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero]
      rfl
    unfold lowerDirectionalResponse
    rw [← he]
    exact le_iSup_of_le u (le_iSup_of_le U.field (le_iSup_of_le hu (le_refl _)))

/-- Positive-dimensional lower-response existence and uniqueness. -/
theorem lowerResponse_existsUnique_pos [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (ha : IsWeightedCoeffOn V a) :
    ∃! A : Mat d, A.PosDef ∧ ∀ e : Vec d,
      ((vecDot e (matVecMul A e) : ℝ) : EReal) = lowerDirectionalResponse a V e := by
  let T := lowerResponseGradient hV.isOpen ha
  let c := (volume V).toReal⁻¹
  have hc : 0 < c := inv_pos.mpr (ENNReal.toReal_pos
    (hV.isOpen.measure_pos volume hne).ne' hV.isBoundedDomain.isBounded.measure_lt_top.ne)
  let A := lowerGramMatrix T c
  have hA : A.PosDef := lowerGramMatrix_posDef T hc
    (lowerResponseGradient_injective hV hne ha)
  have he (e : Vec d) :
      ((vecDot e (matVecMul A e) : ℝ) : EReal) = lowerDirectionalResponse a V e := by
    rw [lowerDirectionalResponse_eq_riesz hV hne ha e, lowerGramMatrix_quadratic]
  refine ⟨A, ⟨hA, he⟩, ?_⟩
  intro M hM
  apply lower_matrix_ext hM.1 hA
  intro e
  exact EReal.coe_injective ((hM.2 e).trans (he e).symm)

/-- Existence and uniqueness of the lower-response matrix, in every dimension. -/
theorem lowerResponse_existsUnique_proved
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn V a) :
    ∃! A : Mat d, A.PosDef ∧ ∀ e : Vec d,
      ((vecDot e (matVecMul A e) : ℝ) : EReal) = lowerDirectionalResponse a V e := by
  cases d with
  | zero => exact lowerResponse_existsUnique_dim_zero a V
  | succ n => exact lowerResponse_existsUnique_pos hV hV₀ ha


end CoarseDeGiorgi.Weighted
