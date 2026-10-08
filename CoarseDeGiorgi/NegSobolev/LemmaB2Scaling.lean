module

public import CoarseDeGiorgi.Statements.SobolevNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Positive scalar normalization of the Sobolev norm. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- Weak derivative arrays commute with multiplication by a constant. -/
theorem lemmaB2_weakDeriv_const_mul {d j : ℕ} {U : Set (Vec d)}
    {w : Vec d → ℝ} {D : (Fin j → Fin d) → Vec d → ℝ}
    (hD : IsWeakDerivArray U j w D) (c : ℝ) :
    IsWeakDerivArray U j (fun x => c * w x) (fun ι x => c * D ι x) := by
  refine ⟨hD.1.smul c, fun ι => ⟨(hD.2 ι).1.smul c, ?_⟩⟩
  intro φ hφ hc hs
  simp only [mul_assoc, integral_const_mul]
  rw [(hD.2 ι).2 φ hφ hc hs]
  ring

/-- Homogeneity of the Euclidean norm of a finite derivative array. -/
theorem lemmaB2_array_const_mul {ι : Type*} [Fintype ι]
    (c : ℝ) (hc : 0 ≤ c) (F : ι → ℝ) :
    Real.sqrt (∑ i, (c * F i) ^ 2) = c * Real.sqrt (∑ i, F i ^ 2) := by
  simp only [mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Positive homogeneity of the array fractional seminorm. -/
theorem lemmaB2_arrayFracSeminorm_const_mul {d : ℕ} {ι : Type*} [Fintype ι]
    (U : Set (Vec d)) (α ξ : ℝ) (hξ : 0 < ξ)
    (F : ι → Vec d → ℝ) (c : ℝ) (hc : 0 < c) :
    arrayFracSeminorm U α ξ (fun i x => c * F i x) =
      ENNReal.ofReal c * arrayFracSeminorm U α ξ F := by
  unfold arrayFracSeminorm
  simp only [← mul_sub, lemmaB2_array_const_mul c hc.le,
    Real.mul_rpow hc.le (Real.sqrt_nonneg _),
    mul_div_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg hc.le ξ)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [ENNReal.rpow_eq_pow]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / ξ),
    ← ENNReal.ofReal_rpow_of_pos hc, ← ENNReal.rpow_mul,
    mul_one_div_cancel hξ.ne', ENNReal.rpow_one]

/-- Scaling by a positive constant can only scale the Sobolev norm by that constant.
This uses admissible arrays in the infimum and does not require the norm to be finite. -/
theorem lemmaB2_sobolevNorm_const_mul_le {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (β ξ : ℝ) (hβ : 0 ≤ β) (hξ : 1 ≤ ξ)
    (w : Vec d → ℝ) (c : ℝ) (hc : 0 < c) :
    sobolevNorm U hU β ξ hβ hξ (fun x => c * w x) ≤
      ENNReal.ofReal c * sobolevNorm U hU β ξ hβ hξ w := by
  have hξpos : 0 < ξ := lt_of_lt_of_le zero_lt_one hξ
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  unfold sobolevNorm
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro D
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro hD
  let Dc : (j : Fin (⌊β⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ :=
    fun j ι x => c * D j ι x
  have hDc : ∀ j : Fin (⌊β⌋₊ + 1),
      IsWeakDerivArray U j (fun x => c * w x) (Dc j) :=
    fun j => lemmaB2_weakDeriv_const_mul (hD j) c
  refine (iInf_le_of_le Dc (iInf_le_of_le hDc le_rfl)).trans_eq ?_
  have hnorm (j : Fin (⌊β⌋₊ + 1)) :
      eLpNorm (fun x => Real.sqrt (∑ ι, Dc j ι x ^ 2)) (ENNReal.ofReal ξ)
        (volume.restrict U) =
      ENNReal.ofReal c * eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2))
        (ENNReal.ofReal ξ) (volume.restrict U) := by
    simp only [Dc, lemmaB2_array_const_mul c hc.le]
    change eLpNorm (c • (fun x => Real.sqrt (∑ ι, D j ι x ^ 2))) _ _ = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_pos hc] using
      eLpNorm_const_smul c (fun x => Real.sqrt (∑ ι, D j ι x ^ 2))
        (ENNReal.ofReal ξ) (volume.restrict U)
  simp_rw [hnorm]
  have hfrac : (if β - ⌊β⌋₊ = 0 then 0 else
      (arrayFracSeminorm U (β - ⌊β⌋₊) ξ (Dc (Fin.last ⌊β⌋₊))).rpow ξ) =
      (ENNReal.ofReal c).rpow ξ * (if β - ⌊β⌋₊ = 0 then 0 else
        (arrayFracSeminorm U (β - ⌊β⌋₊) ξ (D (Fin.last ⌊β⌋₊))).rpow ξ) := by
    split_ifs with ha
    · exact (mul_zero _).symm
    · rw [lemmaB2_arrayFracSeminorm_const_mul U _ ξ hξpos _ c hc]
      exact ENNReal.mul_rpow_of_nonneg _ _ (by exact hξpos.le)
  rw [hfrac]
  simp only [ENNReal.rpow_eq_pow]
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hξpos.le, ← Finset.mul_sum]
  rw [← mul_add, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / ξ),
    ← ENNReal.rpow_mul, mul_one_div_cancel hξpos.ne', ENNReal.rpow_one]

end CoarseDeGiorgi.NegSobolev
