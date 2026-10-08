module

public import CoarseDeGiorgi.NegSobolev.GaussDerivDomination
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Coordinate differential formulas and local domination of Gaussian derivatives. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators Topology

namespace CoarseDeGiorgi.NegSobolev

/-- A coordinate entry of the classical Gaussian derivative array. -/
noncomputable def gaussDerivEntry {d j : ℕ} (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d)
    (x : Vec d) : ℝ :=
  iteratedFDeriv ℝ j (gaussianKernel t ht) x (fun k => basisVec (ι k))

theorem gaussDerivEntry_contDiff {d j : ℕ} (t : ℝ) (ht : 0 < t)
    (ι : Fin j → Fin d) : ContDiff ℝ (⊤ : ℕ∞) (gaussDerivEntry t ht ι) :=
  testNorm_contDiff_deriv_eval (gaussDeriv_contDiff t ht) _

theorem gaussDerivEntry_fderiv_basis {d j : ℕ} (t : ℝ) (ht : 0 < t)
    (ι : Fin j → Fin d) (x : Vec d) (i : Fin d) :
    fderiv ℝ (gaussDerivEntry t ht ι) x (basisVec i) =
      gaussDerivEntry t ht (Fin.cons i ι) x := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j (gaussianKernel (d := d) t ht)) x :=
    ((gaussDeriv_contDiff t ht).differentiable_iteratedFDeriv (m := j)
      (by exact_mod_cast (ENat.natCast_lt_top j))).differentiableAt
  unfold gaussDerivEntry
  rw [hdiff.iteratedFDeriv_succ_apply_left']
  simp only [Fin.cons_zero]
  rfl

theorem gaussDerivEntry_fderiv {d j : ℕ} (t : ℝ) (ht : 0 < t)
    (ι : Fin j → Fin d) (x v : Vec d) :
    fderiv ℝ (gaussDerivEntry t ht ι) x v =
      ∑ i, v i * gaussDerivEntry t ht (Fin.cons i ι) x := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => congrArg (v i * ·)
    (gaussDerivEntry_fderiv_basis t ht ι x i)

theorem gaussDerivEntry_fderiv_bound (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) (x : Vec d),
      ‖fderiv ℝ (gaussDerivEntry t ht ι) x‖ ≤
        (C * t ^ (-(((j + 1 : ℕ) : ℝ) / 2))) * gaussianKernel (2 * t) (by positivity) x := by
  obtain ⟨C, hC, hbound⟩ := gaussDeriv_domination d (j + 1)
  refine ⟨(d + 1) * C, by positivity, fun t ht ι x => ?_⟩
  let B := (C * t ^ (-(((j + 1 : ℕ) : ℝ) / 2))) * gaussianKernel (2 * t) (by positivity) x
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg ht.le _))
    (gaussianKernel_nonneg _ _ _)
  have hb (i : Fin d) : |gaussDerivEntry t ht (Fin.cons i ι) x| ≤ B := hbound t ht _ x
  have hnorm : ‖fderiv ℝ (gaussDerivEntry t ht ι) x‖ ≤ (d : ℝ) * B := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hB)
    intro v
    rw [gaussDerivEntry_fderiv, Real.norm_eq_abs]
    calc
      _ ≤ ∑ i, |v i * gaussDerivEntry t ht (Fin.cons i ι) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, ‖v‖ * B := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
          (hb i) (abs_nonneg _) (norm_nonneg _)
      _ = (d : ℝ) * B * ‖v‖ := by simp; ring
  apply hnorm.trans
  dsimp [B]
  nlinarith [mul_nonneg hB (show (0 : ℝ) ≤ 1 by norm_num)]

/-- A ball whose radius is the square root of the time admits one wider Gaussian
as a common integrable envelope for all shifts of its center. -/
theorem gaussDeriv_gaussian_local {d : ℕ} (s : ℝ) (hs : 0 < s)
    (x x₀ y : Vec d) (hx : ‖x - x₀‖ < Real.sqrt s) :
    gaussianKernel s hs (x - y) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * s) (by positivity) (x₀ - y) := by
  apply gaussianKernel_le_double_time
  have hb : vecNormSq (x₀ - x) ≤ (d : ℝ) * s := by
    unfold vecNormSq vecDot
    have hc (i : Fin d) : (x₀ i - x i) ^ 2 ≤ s := by
      have hi := norm_le_pi_norm (x - x₀) i
      have hsq := sq_le_sq₀ (abs_nonneg ((x - x₀) i)) (Real.sqrt_nonneg s)
      have hi' : |(x - x₀) i| ≤ Real.sqrt s :=
        (show |(x - x₀) i| ≤ ‖x - x₀‖ by simpa only [Real.norm_eq_abs] using hi).trans hx.le
      have h := hsq.mpr hi'
      rw [sq_abs, Real.sq_sqrt hs.le] at h
      simpa only [Pi.sub_apply, sub_sq_comm] using h
    calc
      _ = ∑ i : Fin d, (x₀ i - x i) ^ 2 := by simp only [Pi.sub_apply, pow_two]
      _ ≤ ∑ _i : Fin d, s := Finset.sum_le_sum fun i _ => hc i
      _ = _ := by simp
  have htri := vecNormSq_add_le (x - y) (x₀ - x)
  rw [show x - y + (x₀ - x) = x₀ - y by abel] at htri
  linarith only [htri, hb]

end CoarseDeGiorgi.NegSobolev
