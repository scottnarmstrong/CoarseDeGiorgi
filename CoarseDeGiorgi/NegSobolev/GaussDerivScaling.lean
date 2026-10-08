import CoarseDeGiorgi.Statements.GaussianKernel
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Smoothness and exact derivative scaling of the Gaussian on the product carrier. -/

open Homogenization MeasureTheory
open scoped BigOperators

namespace CoarseDeGiorgi.NegSobolev

/-- The Gaussian is smooth at every positive time. -/
theorem gaussDeriv_contDiff {d : ℕ} (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianKernel (d := d) t ht) := by
  unfold gaussianKernel vecNormSq vecDot
  fun_prop

/-- The Gaussian at time `t` is a dilation of the Gaussian at time one. -/
theorem gaussDeriv_scaling {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    gaussianKernel t ht x =
      t ^ (-((d : ℝ) / 2)) * gaussianKernel 1 zero_lt_one (t ^ (-(1 / 2 : ℝ)) • x) := by
  have hc : (t ^ (-(1 / 2 : ℝ))) ^ 2 = t⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
    exact Real.rpow_neg_one t
  unfold gaussianKernel
  rw [vecNormSq_smul, hc]
  have hpref : (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) =
      t ^ (-((d : ℝ) / 2)) * (4 * Real.pi * 1) ^ (-((d : ℝ) / 2)) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) ht.le, mul_one, mul_comm]
  rw [hpref]
  have hexp : -(vecNormSq x) / (4 * t) = -(t⁻¹ * vecNormSq x) / (4 * 1) := by
    field_simp
  rw [hexp]
  ring

/-- Every classical derivative scales with one extra factor `t^{-1/2}` per order. -/
theorem gaussDeriv_iterated_scaling {d j : ℕ} (t : ℝ) (ht : 0 < t)
    (x : Vec d) (v : Fin j → Vec d) :
    iteratedFDeriv ℝ j (gaussianKernel t ht) x v =
      (t ^ (-((d : ℝ) / 2)) * (t ^ (-(1 / 2 : ℝ))) ^ j) *
        iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one)
          (t ^ (-(1 / 2 : ℝ)) • x) v := by
  let c : ℝ := t ^ (-(1 / 2 : ℝ))
  let A : Vec d →L[ℝ] Vec d := c • ContinuousLinearMap.id ℝ (Vec d)
  have heq : gaussianKernel (d := d) t ht =
      fun y => t ^ (-((d : ℝ) / 2)) • (gaussianKernel 1 zero_lt_one ∘ A) y := by
    funext y
    exact gaussDeriv_scaling t ht y
  have hunit : ContDiff ℝ j (gaussianKernel (d := d) 1 zero_lt_one) :=
    (gaussDeriv_contDiff 1 zero_lt_one).of_le (by simp)
  have hcomp : ContDiff ℝ j (gaussianKernel 1 zero_lt_one ∘ A) := hunit.comp A.contDiff
  rw [heq, iteratedFDeriv_const_smul_apply' hcomp.contDiffAt,
    A.iteratedFDeriv_comp_right hunit x le_rfl]
  change t ^ (-((d : ℝ) / 2)) *
      iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) (c • x) (fun i => c • v i) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact (mul_assoc _ _ _).symm

/-- The combined derivative scaling factor is `t^{-(d+j)/2}`. -/
theorem gaussDeriv_scaling_factor (d j : ℕ) (t : ℝ) (ht : 0 < t) :
    t ^ (-((d : ℝ) / 2)) * (t ^ (-(1 / 2 : ℝ))) ^ j =
      t ^ (-(((d : ℝ) + (j : ℝ)) / 2)) := by
  rw [← Real.rpow_mul_natCast ht.le, ← Real.rpow_add ht]
  congr 1
  ring

/-- Exact scaling of the integral of the absolute value of a derivative entry.
This identity does not assume integrability; its use as a finite bound still
requires integrability of the corresponding derivative at time one. -/
theorem gaussDeriv_integral_abs_scaling {d j : ℕ} (t : ℝ) (ht : 0 < t)
    (v : Fin j → Vec d) :
    (∫ x : Vec d, |iteratedFDeriv ℝ j (gaussianKernel t ht) x v|) =
      t ^ (-((j : ℝ) / 2)) *
        ∫ x : Vec d, |iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x v| := by
  simp_rw [gaussDeriv_iterated_scaling t ht, gaussDeriv_scaling_factor d j t ht,
    abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  rw [integral_const_mul, Measure.integral_comp_smul volume
    (fun x : Vec d => |iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x v|)]
  simp only [Module.finrank_fin_fun, smul_eq_mul]
  have hc : |((t ^ (-(1 / 2 : ℝ))) ^ d)⁻¹| = t ^ ((d : ℝ) / 2) := by
    rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (Real.rpow_nonneg ht.le _) _)),
      ← Real.rpow_mul_natCast ht.le, ← Real.rpow_neg ht.le]
    congr 1
    ring
  rw [hc, ← mul_assoc, ← Real.rpow_add ht]
  congr 2
  ring

end CoarseDeGiorgi.NegSobolev
