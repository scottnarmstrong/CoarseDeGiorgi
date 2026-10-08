module

public import CoarseDeGiorgi.Weighted.UpperSpecNorm
public import CoarseDeGiorgi.Weighted.ResponseBoundsLower
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn

/-! # Simplex means against cube means for positive coefficient fields

If `U ⊆ Q` and `|Q| = d! |U|`, the entrywise mean of a positive definite field over `U` is at most
`d!` times its mean over `Q` as a quadratic form, hence in operator norm. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.CoefficientConditions

variable {d : ℕ} {a : CoeffField d}

theorem isWeightedCoeffOn_mono {U Q : Set (Vec d)} (hUQ : U ⊆ Q)
    (ha : IsWeightedCoeffOn Q a) : IsWeightedCoeffOn U a :=
  ⟨AEStronglyMeasurable.mono_set hUQ ha.1, ae_restrict_of_ae_restrict_of_subset hUQ ha.2.1,
    ha.2.2.1.mono_set hUQ, ha.2.2.2.mono_set hUQ⟩

theorem quadratic_integrable {Q : Set (Vec d)} (ha : IsWeightedCoeffOn Q a) (e : Vec d) :
    IntegrableOn (fun x => vecDot e (matVecMul (a x) e)) Q := by
  have hi (i j : Fin d) := Weighted.response_coefficient_entry_integrable ha i j
  unfold vecDot matVecMul
  exact integrable_finsetSum _ (fun i _ => (integrable_finsetSum _
    (fun j _ => ((hi i j).mul_const (e j)))).const_mul (e i))

theorem quadratic_nonneg_ae {Q : Set (Vec d)} (ha : IsWeightedCoeffOn Q a) (e : Vec d) :
    ∀ᵐ x ∂(volume.restrict Q), 0 ≤ vecDot e (matVecMul (a x) e) := by
  filter_upwards [ha.2.1] with x hx
  simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
    hx.posSemidef.dotProduct_mulVec_nonneg e

theorem volumeAverageMat_posSemidef {U : Set (Vec d)} (ha : IsWeightedCoeffOn U a) :
    (volumeAverageMat U a).PosSemidef := by
  have hq (e : Vec d) : 0 ≤ vecDot e (matVecMul (volumeAverageMat U a) e) := by
    rw [← Weighted.response_quadratic_average ha e]
    unfold volumeAverage
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg_of_ae (quadratic_nonneg_ae ha e))
  have hsym : (volumeAverageMat U a).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, volumeAverageMat, volumeAverage]
    congr 1
    apply integral_congr_ae
    filter_upwards [ha.2.1] with x hx
    exact hx.isHermitian.apply i j |>.symm.trans (by simp) |>.symm
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨hsym, fun x => ?_⟩
  simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using hq x

theorem quadratic_average_le {U Q : Set (Vec d)} (ha : IsWeightedCoeffOn Q a) (hUQ : U ⊆ Q)
    (hvol : volume Q = (d.factorial : ℝ≥0∞) * volume U) (h0 : volume U ≠ 0)
    (htop : volume U ≠ ⊤) (e : Vec d) :
    vecDot e (matVecMul (volumeAverageMat U a) e) ≤
      (d.factorial : ℝ) * vecDot e (matVecMul (volumeAverageMat Q a) e) := by
  rw [← Weighted.response_quadratic_average (isWeightedCoeffOn_mono hUQ ha),
    ← Weighted.response_quadratic_average ha]
  have hint : ∫ x in U, vecDot e (matVecMul (a x) e) ≤ ∫ x in Q, vecDot e (matVecMul (a x) e) :=
    setIntegral_mono_set (quadratic_integrable ha e) (quadratic_nonneg_ae ha e)
      (Filter.Eventually.of_forall hUQ)
  have hpos : 0 < (volume U).toReal := ENNReal.toReal_pos h0 htop
  have hQ : (volume Q).toReal = (d.factorial : ℝ) * (volume U).toReal := by
    rw [hvol, ENNReal.toReal_mul]; simp
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  unfold volumeAverage
  rw [hQ]
  have hI : 0 ≤ ∫ x in Q, vecDot e (matVecMul (a x) e) :=
    integral_nonneg_of_ae (quadratic_nonneg_ae ha e)
  calc (volume U).toReal⁻¹ * ∫ x in U, vecDot e (matVecMul (a x) e)
      ≤ (volume U).toReal⁻¹ * ∫ x in Q, vecDot e (matVecMul (a x) e) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hpos.le)
    _ = _ := by field_simp

theorem norm_average_le {U Q : Set (Vec d)} (ha : IsWeightedCoeffOn Q a) (hUQ : U ⊆ Q)
    (hvol : volume Q = (d.factorial : ℝ≥0∞) * volume U) (h0 : volume U ≠ 0)
    (htop : volume U ≠ ⊤) :
    ‖volumeAverageMat U a‖ ≤ (d.factorial : ℝ) * ‖volumeAverageMat Q a‖ := by
  have hf : (0 : ℝ) ≤ d.factorial := Nat.cast_nonneg _
  have hn : ‖(d.factorial : ℝ) • volumeAverageMat Q a‖ =
      (d.factorial : ℝ) * ‖volumeAverageMat Q a‖ := by
    rw [norm_smul, Real.norm_of_nonneg hf]
  rw [← hn]
  apply Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic
    (volumeAverageMat_posSemidef (isWeightedCoeffOn_mono hUQ ha))
  intro e
  refine (quadratic_average_le ha hUQ hvol h0 htop e).trans (le_of_eq ?_)
  simp only [vecDot, matVecMul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

end CoarseDeGiorgi.CoefficientConditions
