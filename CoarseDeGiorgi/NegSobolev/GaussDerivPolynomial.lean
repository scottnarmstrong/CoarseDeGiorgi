module

public import CoarseDeGiorgi.NegSobolev.GaussDerivScaling
public import CoarseDeGiorgi.NegSobolev.TestNormWeakDeriv
public import CoarseDeGiorgi.NegSobolev.GaussianBasic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Polynomial factors of Gaussian derivatives and their integrability. -/

@[expose] public section

open Homogenization MeasureTheory Polynomial
open scoped BigOperators

namespace CoarseDeGiorgi.NegSobolev

/-- A polynomial times the one-dimensional time-one Gaussian exponential. -/
noncomputable def gaussDerivPolynomialFactor (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  P.eval x * Real.exp (-(x ^ 2 / 4))

/-- Differentiating a polynomial Gaussian preserves the polynomial Gaussian form. -/
theorem gaussDerivPolynomialFactor_hasDerivAt (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (gaussDerivPolynomialFactor P)
      (gaussDerivPolynomialFactor (P.derivative - C (1 / 2) * X * P) x) x := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 4)))
      ((-x / 2) * Real.exp (-(x ^ 2 / 4))) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 4).neg.exp using 1
    · funext y
      dsimp
    · dsimp
      ring
  convert (P.hasDerivAt x).mul he using 1
  · rfl
  · simp only [gaussDerivPolynomialFactor, eval_sub, eval_mul, eval_C, eval_X]
    ring

/-- Polynomial Gaussian factors are integrable. -/
theorem gaussDerivPolynomialFactor_integrable (P : Polynomial ℝ) :
    Integrable (gaussDerivPolynomialFactor P) volume := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    convert hP.add hQ using 1
    funext x
    simp only [gaussDerivPolynomialFactor, eval_add, add_mul, Pi.add_apply]
  | monomial n a =>
    have hi := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)
      (s := (n : ℝ)) (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
    convert hi.const_mul a using 1
    funext x
    simp only [gaussDerivPolynomialFactor, eval_monomial, Real.rpow_natCast]
    rw [show -(x ^ 2 / 4) = -(1 / 4 : ℝ) * x ^ 2 by ring]
    ring

/-- A product of one-dimensional polynomial Gaussian factors is integrable on
product Lebesgue space. -/
theorem gaussDerivPolynomialFactor_prod_integrable {d : ℕ}
    (P : Fin d → Polynomial ℝ) :
    Integrable (fun x : Vec d => ∏ i, gaussDerivPolynomialFactor (P i) (x i)) volume :=
  Integrable.fintype_prod (fun i => gaussDerivPolynomialFactor_integrable (P i))

/-- Taking a coordinate derivative differentiates exactly its polynomial factor. -/
theorem gaussDerivPolynomialFactor_prod_fderiv {d : ℕ} (P : Fin d → Polynomial ℝ)
    (i : Fin d) (x : Vec d) :
    fderiv ℝ (fun y : Vec d => ∏ k, gaussDerivPolynomialFactor (P k) (y k)) x (basisVec i) =
      ∏ k, gaussDerivPolynomialFactor
        (Function.update P i ((P i).derivative - C (1 / 2) * X * P i) k) (x k) := by
  let D (k : Fin d) : Polynomial ℝ := (P k).derivative - C (1 / 2) * X * P k
  have hf (k : Fin d) : HasFDerivAt (fun y : Vec d => gaussDerivPolynomialFactor (P k) (y k))
      (gaussDerivPolynomialFactor (D k) (x k) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) x := by
    have hproj : HasFDerivAt (fun y : Vec d => y k) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) k).hasFDerivAt
    exact HasDerivAt.comp_hasFDerivAt x
      (gaussDerivPolynomialFactor_hasDerivAt (P k) (x k)) hproj
  rw [(HasFDerivAt.finsetProd (u := Finset.univ) (fun k _ => hf k)).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, basisVec_apply]
  rw [Finset.sum_eq_single i]
  · rw [← Finset.mul_prod_erase Finset.univ
      (fun k => gaussDerivPolynomialFactor
        (Function.update P i ((P i).derivative - C (1 / 2) * X * P i) k) (x k))
      (Finset.mem_univ i)]
    simp only [Function.update_self, ite_true, mul_one]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · intro k _ hki
    simp only [ite_eq_right hki, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Every ordered coordinate derivative of the time-one Gaussian is a product
of polynomial Gaussian factors. -/
theorem gaussDeriv_iterated_eq_prod {d j : ℕ} (ι : Fin j → Fin d) :
    ∃ P : Fin d → Polynomial ℝ,
      (fun x : Vec d => iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x
        (fun k => basisVec (ι k))) =
      fun x => ∏ i, gaussDerivPolynomialFactor (P i) (x i) := by
  induction j with
  | zero =>
    refine ⟨fun _ => C ((4 * Real.pi) ^ (-(1 / 2 : ℝ))), ?_⟩
    funext x
    simp only [iteratedFDeriv_zero_apply, gaussianKernel_eq_prod,
      gaussDerivPolynomialFactor, eval_C, mul_one]
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    ring
  | succ j ih =>
    obtain ⟨P, hP⟩ := ih (Fin.tail ι)
    refine ⟨Function.update P (ι 0) ((P (ι 0)).derivative - C (1 / 2) * X * P (ι 0)), ?_⟩
    funext x
    have hdiff : DifferentiableAt ℝ
        (iteratedFDeriv ℝ j (gaussianKernel (d := d) 1 zero_lt_one)) x :=
      ((gaussDeriv_contDiff 1 zero_lt_one).differentiable_iteratedFDeriv (m := j)
        (by exact_mod_cast (ENat.natCast_lt_top j))).differentiableAt
    rw [hdiff.iteratedFDeriv_succ_apply_left']
    change fderiv ℝ (fun y : Vec d => iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) y
      (fun k => basisVec (Fin.tail ι k))) x (basisVec (ι 0)) = _
    rw [hP]
    exact gaussDerivPolynomialFactor_prod_fderiv P (ι 0) x

/-- Every coordinate derivative of the time-one Gaussian is integrable. -/
theorem gaussDeriv_integrable_one {d j : ℕ} (ι : Fin j → Fin d) :
    Integrable (fun x : Vec d => iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x
      (fun k => basisVec (ι k))) volume := by
  obtain ⟨P, hP⟩ := gaussDeriv_iterated_eq_prod ι
  rw [hP]
  exact gaussDerivPolynomialFactor_prod_integrable P

/-- The derivative scaling identity transfers integrability to every positive time. -/
theorem gaussDeriv_integrable {d j : ℕ} (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) :
    Integrable (fun x : Vec d => iteratedFDeriv ℝ j (gaussianKernel t ht) x
      (fun k => basisVec (ι k))) volume := by
  have hi := (gaussDeriv_integrable_one ι).comp_smul
    (Real.rpow_pos_of_pos ht (-(1 / 2 : ℝ))).ne'
  simp_rw [gaussDeriv_iterated_scaling t ht]
  exact hi.const_mul _

/-- Each fixed derivative order has a uniform `L¹` scaling constant, chosen
before the time and the coordinate tuple. -/
theorem gaussDeriv_eLpNorm_one_bound (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d),
      eLpNorm (fun x : Vec d => iteratedFDeriv ℝ j (gaussianKernel t ht) x
        (fun k => basisVec (ι k))) 1 volume ≤ ENNReal.ofReal (C * t ^ (-((j : ℝ) / 2))) := by
  let I (ι : Fin j → Fin d) : ℝ :=
    ∫ x : Vec d, |iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x
      (fun k => basisVec (ι k))|
  have hI (ι : Fin j → Fin d) : 0 ≤ I ι := integral_nonneg fun _ => abs_nonneg _
  refine ⟨1 + ∑ ι, I ι, add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun ι _ => hI ι), fun t ht ι => ?_⟩
  have hi := gaussDeriv_integrable t ht ι
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  simp only [Real.norm_eq_abs]
  rw [gaussDeriv_integral_abs_scaling t ht]
  apply ENNReal.ofReal_le_ofReal
  have hle : I ι ≤ ∑ κ, I κ := Finset.single_le_sum (fun κ _ => hI κ) (Finset.mem_univ ι)
  exact (mul_le_mul_of_nonneg_left
    (hle.trans (le_add_of_nonneg_left zero_le_one)) (Real.rpow_nonneg ht.le _)).trans_eq
    (mul_comm _ _)

end CoarseDeGiorgi.NegSobolev
