import CoarseDeGiorgi.Foundations.Reconstruction.LowestPrimitive

/-! # The lowest-block divergence inverse -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- Recursion implements the ordered tensor telescope: earlier densities, later constants. -/
def lowestKernel (m : ℤ) : (d : ℕ) → Vec d → Vec d
  | 0, _ => fun i => Fin.elim0 i
  | n + 1, v => Fin.cases
      (lowestPrimitive m (v 0) * (lowestMeanDensity m) ^ n)
      (fun i => lowestDensity m (v 0) * lowestKernel m n (Fin.tail v) i)

/-- The coordinate tail is a continuous linear map. -/
def tailLinear (n : ℕ) : Vec (n + 1) →L[ℝ] Vec n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailLinear_basisVec (n : ℕ) (i : Fin n) :
    tailLinear n (basisVec i.succ) = basisVec i := by
  funext j
  simp only [tailLinear, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
    basisVec_apply, Fin.succ_inj]

theorem contDiff_lowestKernel (m : ℤ) (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (lowestKernel m d) := by
  induction d with
  | zero =>
    apply contDiff_pi.mpr
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    apply contDiff_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ((contDiff_lowestPrimitive m).comp ((ContinuousLinearMap.proj (0 : Fin (n + 1)) : Vec (n + 1) →L[ℝ] ℝ).contDiff)).mul contDiff_const
    · exact ((contDiff_lowestDensity m).comp ((ContinuousLinearMap.proj (0 : Fin (n + 1)) : Vec (n + 1) →L[ℝ] ℝ).contDiff)).mul
        (((ContinuousLinearMap.proj j : Vec n →L[ℝ] ℝ).contDiff).comp (ih.comp (tailLinear n).contDiff))

/-- The divergence of the ordered tensor kernel telescopes to density minus global mean. -/
theorem vectorDivergence_lowestKernel (m : ℤ) (d : ℕ) (v : Vec d) :
    vectorDivergence (lowestKernel m d) v =
      (∏ i : Fin d, lowestDensity m (v i)) - (lowestMeanDensity m) ^ d := by
  induction d with
  | zero => simp only [vectorDivergence, Fin.sum_univ_zero, Fin.prod_univ_zero, pow_zero, sub_self]
  | succ n ih =>
    have hK : Differentiable ℝ (lowestKernel m (n + 1)) :=
      (contDiff_lowestKernel m (n + 1)).differentiable (by norm_num)
    have hKn : Differentiable ℝ (lowestKernel m n) :=
      (contDiff_lowestKernel m n).differentiable (by norm_num)
    have hcoord (i : Fin (n + 1)) :
        (fderiv ℝ (lowestKernel m (n + 1)) v (basisVec i)) i =
          fderiv ℝ (fun x => lowestKernel m (n + 1) x i) v (basisVec i) := by
      rw [fderiv_apply (hK v) i]
      rfl
    have hzero : (fderiv ℝ (lowestKernel m (n + 1)) v (basisVec 0)) 0 =
        (lowestDensity m (v 0) - lowestMeanDensity m) * (lowestMeanDensity m) ^ n := by
      rw [hcoord]
      have h := ((hasDerivAt_lowestPrimitive m (v 0)).hasFDerivAt.comp v
        ((ContinuousLinearMap.proj 0 : Vec (n + 1) →L[ℝ] ℝ).hasFDerivAt)).mul_const
          ((lowestMeanDensity m) ^ n)
      change HasFDerivAt (fun x => lowestKernel m (n + 1) x 0) _ v at h
      rw [h.fderiv]
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, basisVec_apply, ite_true, one_mul]
      ring
    have hsucc (i : Fin n) :
        (fderiv ℝ (lowestKernel m (n + 1)) v (basisVec i.succ)) i.succ =
          lowestDensity m (v 0) * (fderiv ℝ (lowestKernel m n) (Fin.tail v) (basisVec i)) i := by
      have h0i : (0 : Fin (n + 1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero i)
      rw [hcoord]
      have hp := ((contDiff_lowestDensity m).differentiable (by norm_num) (v 0)).hasFDerivAt.comp v
        ((ContinuousLinearMap.proj 0 : Vec (n + 1) →L[ℝ] ℝ).hasFDerivAt)
      have hk := (ContinuousLinearMap.proj i : Vec n →L[ℝ] ℝ).hasFDerivAt.comp v
        ((hKn (Fin.tail v)).hasFDerivAt.comp v (tailLinear n).hasFDerivAt)
      have h := hp.mul hk
      change HasFDerivAt (fun x => lowestKernel m (n + 1) x i.succ) _ v at h
      rw [h.fderiv]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        basisVec_apply, h0i, ite_false, mul_zero, add_zero, tailLinear_basisVec,
        Function.comp_apply, map_zero]
    rw [vectorDivergence, Fin.sum_univ_succ, hzero]
    simp only [hsucc]
    rw [← Finset.mul_sum]
    change _ + lowestDensity m (v 0) * vectorDivergence (lowestKernel m n) (Fin.tail v) = _
    rw [ih, Fin.prod_univ_succ, pow_succ]
    simp only [Fin.tail]
    ring

/-- The lowest kernel is periodic in every coordinate, including the primitive factor. -/
theorem lowestKernel_add_period (m : ℤ) (d : ℕ) (j : Fin d) (v : Vec d) :
    lowestKernel m d (v + (2 * auxSide m) • basisVec j) = lowestKernel m d v := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    let P := 2 * auxSide m
    have h0succ (k : Fin n) : (0 : Fin (n + 1)) ≠ k.succ := Ne.symm (Fin.succ_ne_zero k)
    have htail0 : Fin.tail (v + P • basisVec (0 : Fin (n + 1))) = Fin.tail v := by
      funext i
      simp only [Fin.tail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply,
        Fin.succ_ne_zero, ite_false, mul_zero, add_zero]
    have htailsucc (k : Fin n) : Fin.tail (v + P • basisVec k.succ) =
        Fin.tail v + P • basisVec k := by
      funext i
      simp only [Fin.tail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply, Fin.succ_inj]
    dsimp only [P] at htail0 htailsucc
    refine Fin.cases ?_ (fun k => ?_) j
    · funext i
      refine Fin.cases ?_ (fun k => ?_) i
      · simp only [lowestKernel, Fin.cases_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          basisVec_apply, ite_true, mul_one]
        rw [(periodic_lowestPrimitive m) (v 0)]
      · simp only [lowestKernel, Fin.cases_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          basisVec_apply, ite_true, mul_one]
        rw [htail0, (periodic_lowestDensity m) (v 0)]
    · funext i
      refine Fin.cases ?_ (fun a => ?_) i
      · simp only [lowestKernel, Fin.cases_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          basisVec_apply, h0succ, ite_false, mul_zero, add_zero]
      · simp only [lowestKernel, Fin.cases_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          basisVec_apply, h0succ, ite_false, mul_zero, add_zero]
        rw [htailsucc, ih]

/-- Exact divergence identity for the lowest block. -/
theorem vectorDivergence_lowestKernel_eq_periodicRho (m : ℤ) (d : ℕ) (v : Vec d) :
    vectorDivergence (lowestKernel m d) v =
      periodicRho m (auxSide m) v - ((2 * auxSide m) ^ d)⁻¹ := by
  rw [vectorDivergence_lowestKernel]
  simp only [lowestDensity_eq, periodicRho, scaledRho_eq_prod, wrapBox, lowestMeanDensity, inv_pow]

end

end CoarseDeGiorgi.Foundations.Reconstruction
