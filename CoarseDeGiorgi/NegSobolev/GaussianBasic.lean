module

public import CoarseDeGiorgi.Statements.GaussianKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic

/-! # Elementary estimates for the Gaussian kernel

All distances here use `vecNormSq`, the Euclidean squared length on `Vec d`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators

namespace CoarseDeGiorgi.NegSobolev

/-- The Gaussian is strictly positive at every point. -/
theorem gaussianKernel_pos {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    0 < gaussianKernel t ht x := by
  unfold gaussianKernel
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- In particular the Gaussian is nonnegative. -/
theorem gaussianKernel_nonneg {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    0 ≤ gaussianKernel t ht x := (gaussianKernel_pos t ht x).le

/-- Its maximum is the normalization factor, attained at the origin. -/
theorem gaussianKernel_le_prefactor {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    gaussianKernel t ht x ≤ (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) := by
  unfold gaussianKernel
  apply mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (vecNormSq_nonneg x))
    (by positivity)

/-- The Gaussian is an even function. -/
theorem gaussianKernel_neg {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    gaussianKernel t ht (-x) = gaussianKernel t ht x := by
  simp only [gaussianKernel, vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]

/-- A squared-distance bound gives the lower estimate used on every cell. -/
theorem gaussianKernel_lower_of_sq_le {d : ℕ} (t : ℝ) (ht : 0 < t)
    (x : Vec d) (hx : vecNormSq x ≤ (d : ℝ) * t) :
    (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) * Real.exp (-((d : ℝ) / 4)) ≤
      gaussianKernel t ht x := by
  unfold gaussianKernel
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  apply Real.exp_le_exp.mpr
  apply (le_div_iff₀ (by positivity : 0 < 4 * t)).mpr
  nlinarith only [hx]

/-- Continuity on the product carrier, without choosing a norm convention. -/
theorem continuous_gaussianKernel {d : ℕ} (t : ℝ) (ht : 0 < t) :
    Continuous (gaussianKernel (d := d) t ht) := by
  unfold gaussianKernel vecNormSq vecDot
  fun_prop

/-- Gaussian comparison at times `t` and `2t`, given the squared-distance estimate.
This separates the scalar arithmetic from the geometry of a cell. -/
theorem gaussianKernel_le_double_time {d : ℕ} (t : ℝ) (ht : 0 < t)
    (u v : Vec d) (h : vecNormSq v ≤ 2 * vecNormSq u + 2 * (d : ℝ) * t) :
    gaussianKernel t ht u ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * t) (by positivity) v := by
  have hbase : 0 < 4 * Real.pi * t := by positivity
  have hpref : (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) =
      (2 : ℝ) ^ ((d : ℝ) / 2) *
        (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2)) := by
    rw [show 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hbase.le]
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp only [add_neg_cancel, Real.rpow_zero, one_mul]
  have hexp : -(vecNormSq u) / (4 * t) ≤
      (d : ℝ) / 4 + -(vecNormSq v) / (4 * (2 * t)) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * t)).mpr
    field_simp
    nlinarith only [h]
  unfold gaussianKernel
  rw [hpref]
  calc
    _ ≤ ((2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2))) *
        Real.exp ((d : ℝ) / 4 + -(vecNormSq v) / (4 * (2 * t))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- A pair of points at squared distance at most `dt` gives the comparison
needed to average the Gaussian over a cell. -/
theorem gaussianKernel_compare_of_sq_sub_le {d : ℕ} (t : ℝ) (ht : 0 < t)
    (x y z : Vec d) (hyz : vecNormSq (y - z) ≤ (d : ℝ) * t) :
    gaussianKernel t ht (x - y) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * t) (by positivity) (x - z) := by
  apply gaussianKernel_le_double_time
  have htri := vecNormSq_add_le (x - y) (y - z)
  rw [sub_add_sub_cancel] at htri
  linarith only [htri, hyz]

/-- Product representation on the actual product-volume carrier `Fin d → ℝ`. -/
theorem gaussianKernel_eq_prod {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    gaussianKernel t ht x =
      ∏ i : Fin d, ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(1 / (4 * t)) * (x i) ^ 2)) := by
  unfold gaussianKernel
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_mul_natCast (by positivity : 0 ≤ 4 * Real.pi * t),
    ← Real.exp_sum]
  congr 1
  · congr 1
    ring
  · unfold vecNormSq vecDot
    simp only [pow_two]
    rw [← Finset.mul_sum]
    congr 1
    ring

/-- The Gaussian is integrable for every positive time. -/
theorem integrable_gaussianKernel {d : ℕ} (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianKernel (d := d) t ht) volume := by
  have heq := funext (gaussianKernel_eq_prod (d := d) t ht)
  rw [heq]
  exact Integrable.fintype_prod (fun _ =>
    (integrable_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * t))).const_mul _)

/-- The Gaussian has total mass one, including dimension zero. -/
theorem integral_gaussianKernel {d : ℕ} (t : ℝ) (ht : 0 < t) :
    ∫ x : Vec d, gaussianKernel t ht x = 1 := by
  simp_rw [gaussianKernel_eq_prod]
  change (∫ x : Fin d → ℝ, ∏ i,
    (fun u : ℝ => (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(1 / (4 * t)) * u ^ 2)) (x i)) = 1
  rw [integral_fintype_prod_volume_eq_pow (ι := Fin d)
    (fun u : ℝ => (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(1 / (4 * t)) * u ^ 2))]
  have hscalar : ∫ x : ℝ, (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(1 / (4 * t)) * x ^ 2) = 1 := by
    rw [integral_const_mul, integral_gaussian]
    have hden : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by
      rw [one_div, div_inv_eq_mul]
      ring
    rw [hden, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity : 0 < 4 * Real.pi * t)]
    norm_num
  rw [hscalar, one_pow]

/-- At time equal to the square of a side length, the prefactor times the cube
volume is independent of that length. -/
theorem gaussianKernel_prefactor_mul_side_volume (d : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    (4 * Real.pi * ℓ ^ 2) ^ (-((d : ℝ) / 2)) * ℓ ^ d =
      (4 * Real.pi) ^ (-((d : ℝ) / 2)) := by
  have hpow : (ℓ ^ 2) ^ (-((d : ℝ) / 2)) = (ℓ ^ d)⁻¹ := by
    rw [← Real.rpow_natCast ℓ 2, ← Real.rpow_mul hℓ.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-((d : ℝ) / 2)) = -(d : ℝ) by ring,
      Real.rpow_neg hℓ.le, Real.rpow_natCast]
  rw [Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi) (sq_nonneg ℓ), hpow,
    mul_assoc, inv_mul_cancel₀ (pow_ne_zero d hℓ.ne'), mul_one]

end CoarseDeGiorgi.NegSobolev
