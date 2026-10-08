module

public import CoarseDeGiorgi.Foundations.Reconstruction.FineKernelDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Divergence of the physical-space fine kernel -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-- Sum of the coordinate derivatives on the sup-norm carrier. -/
def vectorDivergence (K : Vec d → Vec d) (v : Vec d) : ℝ :=
  ∑ i : Fin d, (fderiv ℝ K v (basisVec i)) i

theorem sum_smul_basisVec (v : Vec d) : (∑ i : Fin d, v i • basisVec i) = v := by
  exact (pi_eq_sum_univ' v).symm

theorem sum_mul_apply_basisVec (L : Vec d →L[ℝ] ℝ) (v : Vec d) :
    (∑ i : Fin d, L (basisVec i) * v i) = L v := by
  calc
    (∑ i : Fin d, L (basisVec i) * v i) = L (∑ i : Fin d, v i • basisVec i) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, mul_comm]
    _ = L v := congrArg L (sum_smul_basisVec v)

theorem vectorDivergence_fineKernelIntegrand (t : ℝ) (v : Vec d) :
    vectorDivergence (fineKernelIntegrand t) v =
      t⁻¹ * (fderiv ℝ (scaledRho t) v) v + (d : ℝ) * (scaledRho t v * t⁻¹) := by
  unfold vectorDivergence
  rw [(hasFDerivAt_fineKernelIntegrand t v).fderiv]
  simp only [fineKernelIntegrandDeriv, add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    basisVec_apply, ite_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  calc
    (∑ i : Fin d, (fderiv ℝ (scaledRho t) v) (basisVec i) * (t⁻¹ * v i)) =
        t⁻¹ * ∑ i : Fin d, (fderiv ℝ (scaledRho t) v) (basisVec i) * v i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = t⁻¹ * (fderiv ℝ (scaledRho t) v) v := by rw [sum_mul_apply_basisVec]

theorem hasDerivAt_scaledRho_scale {t : ℝ} (ht : t ≠ 0) (v : Vec d) :
    HasDerivAt (fun s => scaledRho s v) (-vectorDivergence (fineKernelIntegrand t) v) t := by
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t⁻¹ ^ 2)) t := by
    simpa only [inv_pow] using hasDerivAt_inv ht
  have hr := (contDiff_reconstructionRho (d := d)).differentiable (by norm_num)
  have hρ := (hr (t⁻¹ • v)).hasFDerivAt.comp_hasDerivAt t (hinv.smul_const v)
  have hprod := (hinv.pow d).mul hρ
  have hp : (d : ℝ) * t⁻¹ ^ (d - 1) * t⁻¹ ^ 2 = (d : ℝ) * t⁻¹ ^ (d + 1) := by
    cases d with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]; ring
  have hderiv : (d : ℝ) * t⁻¹ ^ (d - 1) * (-(t⁻¹ ^ 2)) * reconstructionRho (t⁻¹ • v) +
      t⁻¹ ^ d * (fderiv ℝ reconstructionRho (t⁻¹ • v)) (-(t⁻¹ ^ 2) • v) =
        -vectorDivergence (fineKernelIntegrand t) v := by
    rw [vectorDivergence_fineKernelIntegrand, fderiv_scaledRho]
    simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul, scaledRho, ← inv_pow]
    rw [mul_neg, ← mul_assoc, hp]
    simp only [pow_succ]
    ring
  dsimp only [Function.comp_apply, Pi.pow_apply] at hprod
  rw [hderiv] at hprod
  convert hprod using 1
  funext s
  simp only [scaledRho, Pi.mul_apply, Pi.pow_apply, Function.comp_apply, inv_pow]

/-- The integral kernel inverts the difference between adjacent smoothing scales. -/
theorem vectorDivergence_fineKernel {h : ℝ} (hh : 0 < h) (v : Vec d) :
    vectorDivergence (fineKernel h) v = scaledRho h v - scaledRho (3 * h) v := by
  let diag (i : Fin d) : (Vec d →L[ℝ] Vec d) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.apply ℝ (Vec d) (basisVec i))
  have hD : IntegrableOn (fun t => fineKernelIntegrandDeriv t v) (Set.Icc h (3 * h)) volume :=
    (continuousOn_fineKernelIntegrandDeriv hh v).integrableOn_Icc
  have hdiag (i : Fin d) : IntegrableOn (fun t => diag i (fineKernelIntegrandDeriv t v))
      (Set.Icc h (3 * h)) volume := (diag i).integrable_comp hD
  have htrace : (fun t => vectorDivergence (fineKernelIntegrand t) v) =
      fun t => ∑ i : Fin d, diag i (fineKernelIntegrandDeriv t v) := by
    funext t
    unfold vectorDivergence
    rw [(hasFDerivAt_fineKernelIntegrand t v).fderiv]
    rfl
  have hint : IntegrableOn (fun t => vectorDivergence (fineKernelIntegrand t) v)
      (Set.Icc h (3 * h)) volume := by
    rw [htrace]
    exact integrable_finsetSum _ fun i _ => hdiag i
  have hdiv : vectorDivergence (fineKernel h) v =
      ∫ t in Set.Icc h (3 * h), vectorDivergence (fineKernelIntegrand t) v ∂volume := by
    change (∑ i : Fin d, (fderiv ℝ (fineKernel h) v (basisVec i)) i) = _
    rw [fderiv_fineKernel hh]
    change (∑ i : Fin d, diag i (∫ t in Set.Icc h (3 * h), fineKernelIntegrandDeriv t v ∂volume)) = _
    rw [htrace]
    rw [integral_finsetSum _ (fun i _ => hdiag i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact ((diag i).integral_comp_comm hD).symm
  have hle : h ≤ 3 * h := by linarith
  have hint' : IntegrableOn (fun t => -vectorDivergence (fineKernelIntegrand t) v)
      (Set.uIcc h (3 * h)) volume := by
    rw [Set.uIcc_of_le hle]
    exact hint.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := h) (b := 3 * h)
    (f := fun t => scaledRho t v)
    (f' := fun t => -vectorDivergence (fineKernelIntegrand t) v)
    (fun t ht => by
      have hti : t ∈ Set.Icc h (3 * h) := by simpa only [Set.uIcc_of_le hle] using ht
      exact hasDerivAt_scaledRho_scale (ne_of_gt (hh.trans_le hti.1)) v)
    hint'.intervalIntegrable
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_of_le hle,
    ← integral_Icc_eq_integral_Ioc, ← hdiv] at hFTC
  linarith

end

end CoarseDeGiorgi.Foundations.Reconstruction
