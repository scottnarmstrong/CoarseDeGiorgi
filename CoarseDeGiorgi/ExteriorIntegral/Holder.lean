import CoarseDeGiorgi.Weighted.Energy
import CoarseDeGiorgi.Statements.WeightedEnergy
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Cauchy-Schwarz for weighted pairings in `[0, ∞]` -/

namespace CoarseDeGiorgi.ExteriorIntegral

open Homogenization MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem holderConjugate_two_two : Real.HolderConjugate 2 2 := by
  rw [Real.holderConjugate_iff]
  norm_num

/-- Lebesgue-integral Cauchy-Schwarz for the weighted pairing, with no finiteness hypothesis. -/
theorem lintegral_pairing_le {V : Set (Vec d)} {a : CoeffField d}
    (ha : IsWeightedCoeffOn V a) {X Y : Vec d → Vec d}
    (hX : AEStronglyMeasurable X (volume.restrict V))
    (hY : AEStronglyMeasurable Y (volume.restrict V)) :
    ∫⁻ x in V, ENNReal.ofReal |vecDot (X x) (matVecMul (a x) (Y x))| ≤
      (weightedEnergy a V X) ^ (1 / 2 : ℝ) * (weightedEnergy a V Y) ^ (1 / 2 : ℝ) := by
  have h0X := Weighted.quadratic_nonneg ha X
  have h0Y := Weighted.quadratic_nonneg ha Y
  have hqX := (Weighted.quadratic_aestronglyMeasurable ha hX).aemeasurable
  have hqY := (Weighted.quadratic_aestronglyMeasurable ha hY).aemeasurable
  let fX : Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.sqrt (vecDot (X x) (matVecMul (a x) (X x))))
  let fY : Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.sqrt (vecDot (Y x) (matVecMul (a x) (Y x))))
  have hfX : AEMeasurable fX (volume.restrict V) :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hqX).ennreal_ofReal
  have hfY : AEMeasurable fY (volume.restrict V) :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hqY).ennreal_ofReal
  have hbound : ∀ᵐ x ∂(volume.restrict V),
      ENNReal.ofReal |vecDot (X x) (matVecMul (a x) (Y x))| ≤ (fX * fY) x := by
    filter_upwards [ha.2.1, h0X] with x hx hzero
    have hcs := hx.star_dotProduct_mulVec_mul_le (X x) (Y x)
    have hcs' : vecDot (X x) (matVecMul (a x) (Y x)) ^ 2 ≤
        vecDot (X x) (matVecMul (a x) (X x)) * vecDot (Y x) (matVecMul (a x) (Y x)) := by
      simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec, pow_two] using hcs
    have : |vecDot (X x) (matVecMul (a x) (Y x))| ≤
        Real.sqrt (vecDot (X x) (matVecMul (a x) (X x))) *
          Real.sqrt (vecDot (Y x) (matVecMul (a x) (Y x))) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact (Real.sqrt_le_sqrt hcs').trans_eq (Real.sqrt_mul hzero _)
    simp only [Pi.mul_apply, fX, fY]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal this
  have hsq (Z : Vec d → Vec d) (h0 : ∀ᵐ x ∂(volume.restrict V),
      0 ≤ vecDot (Z x) (matVecMul (a x) (Z x))) :
      ∫⁻ x in V, (ENNReal.ofReal (Real.sqrt (vecDot (Z x) (matVecMul (a x) (Z x))))) ^
        (2 : ℝ) = weightedEnergy a V Z := by
    unfold weightedEnergy
    apply lintegral_congr_ae
    filter_upwards [h0] with x hx
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt hx]
  calc ∫⁻ x in V, ENNReal.ofReal |vecDot (X x) (matVecMul (a x) (Y x))|
      ≤ ∫⁻ x in V, (fX * fY) x := lintegral_mono_ae hbound
    _ ≤ (∫⁻ x in V, fX x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∫⁻ x in V, fY x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq _ holderConjugate_two_two hfX hfY
    _ = _ := by
      rw [hsq X h0X, hsq Y h0Y]

end

end CoarseDeGiorgi.ExteriorIntegral
