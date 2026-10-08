import CoarseDeGiorgi.NegSobolev.GaussDerivPolynomial
import CoarseDeGiorgi.NegSobolev.GaussDerivLp
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! A wider Gaussian dominates each fixed order of Gaussian derivatives. -/

open Homogenization MeasureTheory Polynomial Filter
open scoped BigOperators Topology

namespace CoarseDeGiorgi.NegSobolev

private theorem polynomial_gaussian_bounded (P : Polynomial ℝ) (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |P.eval x| * Real.exp (-b * x ^ 2) ≤ C := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨CP, hCP, hP⟩ := hP
    obtain ⟨CQ, hCQ, hQ⟩ := hQ
    refine ⟨CP + CQ, add_nonneg hCP hCQ, fun x => ?_⟩
    rw [eval_add]
    calc
      _ ≤ (|P.eval x| + |Q.eval x|) * Real.exp (-b * x ^ 2) :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.exp_nonneg _)
      _ = _ := add_mul _ _ _
      _ ≤ _ := add_le_add (hP x) (hQ x)
  | monomial n a =>
    let f : ZeroAtInftyContinuousMap ℝ ℝ := {
      toFun := fun x => |x| ^ n * Real.exp (-b * x ^ 2)
      continuous_toFun := by fun_prop
      zero_at_infty' := by
        simpa only [Real.rpow_natCast] using
          tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hb (n : ℝ) }
    refine ⟨|a| * ‖f.toBCF‖, mul_nonneg (abs_nonneg _) (norm_nonneg _), fun x => ?_⟩
    have hx := f.toBCF.norm_coe_le_norm x
    have hfx : 0 ≤ f x := mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_nonneg _)
    change ‖f x‖ ≤ ‖f.toBCF‖ at hx
    rw [Real.norm_of_nonneg hfx] at hx
    simp only [eval_monomial, abs_mul, abs_pow]
    change |a| * |x| ^ n * Real.exp (-b * x ^ 2) ≤ _
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

/-- At time one, a Gaussian of twice the variance dominates every fixed
coordinate derivative. The constant is uniform over the coordinate tuples. -/
theorem gaussDeriv_domination_one (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Fin j → Fin d) (x : Vec d),
      |iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x
        (fun k => basisVec (ι k))| ≤ C * gaussianKernel 2 (by norm_num) x := by
  have hentry (ι : Fin j → Fin d) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x : Vec d,
      |iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x
        (fun k => basisVec (ι k))| ≤ A * gaussianKernel 2 (by norm_num) x := by
    obtain ⟨P, hP⟩ := gaussDeriv_iterated_eq_prod ι
    have hbound (i : Fin d) := polynomial_gaussian_bounded (P i) (1 / 8) (by norm_num)
    choose B hB hPB using hbound
    let a : ℝ := (4 * Real.pi * 2) ^ (-((d : ℝ) / 2))
    have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
    refine ⟨(∏ i, B i) / a, div_nonneg (Finset.prod_nonneg fun i _ => hB i) ha.le, fun x => ?_⟩
    have hprod : ∏ i, (|(P i).eval (x i)| * Real.exp (-(1 / 8 : ℝ) * x i ^ 2)) ≤
        ∏ i, B i := Finset.prod_le_prod₀
      (fun i _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) (fun i _ => hPB i (x i))
    have heq : |iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x
          (fun k => basisVec (ι k))| =
        (∏ i, (|(P i).eval (x i)| * Real.exp (-(1 / 8 : ℝ) * x i ^ 2))) *
          Real.exp (-vecNormSq x / 8) := by
      change |(fun x : Vec d => iteratedFDeriv ℝ j (gaussianKernel 1 zero_lt_one) x
        (fun k => basisVec (ι k))) x| = _
      rw [hP]
      simp only [Finset.abs_prod, gaussDerivPolynomialFactor, abs_mul,
        abs_of_nonneg (Real.exp_nonneg _), Finset.prod_mul_distrib, ← Real.exp_sum]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      unfold vecNormSq vecDot
      simp only [← pow_two]
      ring_nf
      simp only [← Finset.sum_mul]
      ring
    rw [heq]
    unfold gaussianKernel
    change _ ≤ (∏ i, B i) / a * (a * Real.exp (-vecNormSq x / (4 * 2)))
    rw [show (4 : ℝ) * 2 = 8 by norm_num, ← mul_assoc, div_mul_cancel₀ _ ha.ne']
    exact mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
  choose A hA hentry using hentry
  refine ⟨1 + ∑ ι, A ι, add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun ι _ => hA ι), fun ι x => ?_⟩
  refine (hentry ι x).trans ?_
  apply mul_le_mul_of_nonneg_right _ (gaussianKernel_nonneg _ _ _)
  exact (Finset.single_le_sum (fun κ _ => hA κ) (Finset.mem_univ ι)).trans
    (le_add_of_nonneg_left zero_le_one)

private theorem gaussian_two_scaling {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    t ^ (-((d : ℝ) / 2)) * gaussianKernel 2 (by norm_num)
      (t ^ (-(1 / 2 : ℝ)) • x) = gaussianKernel (2 * t) (by positivity) x := by
  have hc : (t ^ (-(1 / 2 : ℝ))) ^ 2 = t⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
    exact Real.rpow_neg_one t
  have hpref : (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2)) =
      t ^ (-((d : ℝ) / 2)) * (4 * Real.pi * 2) ^ (-((d : ℝ) / 2)) := by
    rw [show 4 * Real.pi * (2 * t) = (4 * Real.pi * 2) * t by ring,
      Real.mul_rpow (by positivity : 0 ≤ 4 * Real.pi * 2) ht.le, mul_comm]
  unfold gaussianKernel
  rw [vecNormSq_smul, hc, hpref]
  have hexp : -(t⁻¹ * vecNormSq x) / (4 * 2) = -vecNormSq x / (4 * (2 * t)) := by
    field_simp
  rw [hexp]
  ring

/-- Derivatives at every positive time are dominated by a wider Gaussian, with
the uniform derivative scale `t^{-j/2}`. -/
theorem gaussDeriv_domination (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) (x : Vec d),
      |iteratedFDeriv ℝ j (gaussianKernel t ht) x (fun k => basisVec (ι k))| ≤
        (C * t ^ (-((j : ℝ) / 2))) * gaussianKernel (2 * t) (by positivity) x := by
  obtain ⟨C, hC, hbound⟩ := gaussDeriv_domination_one d j
  refine ⟨C, hC, fun t ht ι x => ?_⟩
  have hj : (t ^ (-(1 / 2 : ℝ))) ^ j = t ^ (-((j : ℝ) / 2)) := by
    rw [← Real.rpow_mul_natCast ht.le]
    congr 1
    ring
  rw [gaussDeriv_iterated_scaling t ht, abs_mul,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (pow_nonneg (Real.rpow_nonneg ht.le _) _)), hj]
  calc
    _ ≤ (t ^ (-((d : ℝ) / 2)) * t ^ (-((j : ℝ) / 2))) *
        (C * gaussianKernel 2 (by norm_num) (t ^ (-(1 / 2 : ℝ)) • x)) :=
      mul_le_mul_of_nonneg_left (hbound ι _) (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _))
    _ = (C * t ^ (-((j : ℝ) / 2))) *
        (t ^ (-((d : ℝ) / 2)) * gaussianKernel 2 (by norm_num) (t ^ (-(1 / 2 : ℝ)) • x)) := by ring
    _ = _ := by rw [gaussian_two_scaling t ht]

/-- Each Gaussian derivative belongs to every positive finite Lebesgue class. -/
theorem gaussDeriv_memLp_iterated {d j : ℕ} (t : ℝ) (ht : 0 < t)
    (ι : Fin j → Fin d) (r : ℝ) (hr : 0 < r) :
    MemLp (fun x : Vec d => iteratedFDeriv ℝ j (gaussianKernel t ht) x
      (fun k => basisVec (ι k))) (ENNReal.ofReal r) volume := by
  obtain ⟨C, hC, hbound⟩ := gaussDeriv_domination d j
  have hk := (gaussDeriv_memLp (d := d) (2 * t) (by positivity) r hr).const_smul
    (C * t ^ (-((j : ℝ) / 2)))
  apply hk.mono'
    (testNorm_contDiff_deriv_eval (gaussDeriv_contDiff t ht) _).continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul] using hbound t ht ι x

end CoarseDeGiorgi.NegSobolev
