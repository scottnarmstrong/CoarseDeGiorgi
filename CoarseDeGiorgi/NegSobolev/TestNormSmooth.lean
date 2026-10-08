import CoarseDeGiorgi.NegSobolev.TestNormConvolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! Differentiation of Gaussian convolutions with arbitrary finite-exponent input. -/

open Homogenization MeasureTheory Filter
open scoped BigOperators Topology

namespace CoarseDeGiorgi.NegSobolev

theorem testNorm_gaussDeriv_hasFDerivAt {d j : ℕ} (r : ℝ) (hr : 1 < r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) (x₀ : Vec d) :
    HasFDerivAt (fun x => ∫ y, gaussDerivEntry t ht ι (x - y) * g y)
      (∫ y, g y • fderiv ℝ (gaussDerivEntry t ht ι) (x₀ - y)) x₀ := by
  obtain ⟨C, hC, hbound⟩ := gaussDerivEntry_fderiv_bound d j
  let A := C * t ^ (-(((j + 1 : ℕ) : ℝ) / 2))
  let B := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hk := gaussDerivEntry_contDiff t ht ι
  have hD : Continuous (fderiv ℝ (gaussDerivEntry t ht ι)) :=
    hk.continuous_fderiv (by norm_num)
  have hDm (x : Vec d) : AEStronglyMeasurable
      (fun y => g y • fderiv ℝ (gaussDerivEntry t ht ι) (x - y)) volume :=
    hg.aestronglyMeasurable.smul ((hD.comp (by fun_prop)).aestronglyMeasurable)
  have hi := testNorm_gaussian_mul_integrable r hr hg (2 * (2 * t)) (by positivity) x₀
  have henv : Integrable (fun y => (A * B) *
      (gaussianKernel (2 * (2 * t)) (by positivity) (x₀ - y) * |g y|)) volume := hi.const_mul _
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x₀ (Real.sqrt (2 * t)))
    (bound := fun y => (A * B) *
      (gaussianKernel (2 * (2 * t)) (by positivity) (x₀ - y) * |g y|))
    (Metric.ball_mem_nhds _ (Real.sqrt_pos.mpr (by positivity)))
  · exact Eventually.of_forall fun x =>
      (hk.continuous.comp (by fun_prop)).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact testNorm_convolution_integrable r hr
      (gaussDeriv_memLp_iterated t ht ι _ (Real.HolderConjugate.conjExponent hr).symm.pos) hg x₀
  · exact hDm x₀
  · exact Eventually.of_forall fun y x hx => by
      rw [norm_smul, Real.norm_eq_abs]
      have hb := hbound t ht ι (x - y)
      have hl := gaussDeriv_gaussian_local (2 * t) (by positivity) x x₀ y
        (by simpa only [Metric.mem_ball, dist_eq_norm] using hx)
      calc
        _ ≤ |g y| * (A * gaussianKernel (2 * t) (by positivity) (x - y)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ ≤ |g y| * (A * (B * gaussianKernel (2 * (2 * t)) (by positivity) (x₀ - y))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hA) (abs_nonneg _)
        _ = _ := by ring
  · exact henv
  · exact Eventually.of_forall fun y x _ => by
      convert (((hk.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const y)).mul_const (g y)) using 1 <;>
        simp only [ContinuousLinearMap.comp_id, mul_comm, Function.comp_def, id_eq]

theorem testNorm_gaussDeriv_fderiv_apply {d j : ℕ} (r : ℝ) (hr : 1 < r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) (x v : Vec d) :
    fderiv ℝ (fun x => ∫ y, gaussDerivEntry t ht ι (x - y) * g y) x v =
      ∑ i, v i * ∫ y, gaussDerivEntry t ht (Fin.cons i ι) (x - y) * g y := by
  have hD := testNorm_gaussDeriv_hasFDerivAt r hr g hg t ht ι x
  rw [hD.fderiv]
  have hm : AEStronglyMeasurable
      (fun y => g y • fderiv ℝ (gaussDerivEntry t ht ι) (x - y)) volume :=
    hg.aestronglyMeasurable.smul
      (((gaussDerivEntry_contDiff t ht ι).continuous_fderiv (by norm_num)).comp
        (by fun_prop)).aestronglyMeasurable
  obtain ⟨C, hC, hb⟩ := gaussDerivEntry_fderiv_bound d j
  have hi := testNorm_gaussian_mul_integrable r hr hg (2 * t) (by positivity) x
  have hDi : Integrable (fun y => g y • fderiv ℝ (gaussDerivEntry t ht ι) (x - y)) volume :=
    (hi.const_mul (C * t ^ (-(((j + 1 : ℕ) : ℝ) / 2)))).mono' hm
      (Eventually.of_forall fun y => by
        rw [norm_smul, Real.norm_eq_abs]
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb t ht ι (x - y)) (abs_nonneg (g y)))
  rw [ContinuousLinearMap.integral_apply hDi]
  simp_rw [smul_apply, smul_eq_mul, gaussDerivEntry_fderiv,
    Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    simp_rw [show ∀ y, g y * (v i * gaussDerivEntry t ht (Fin.cons i ι) (x - y)) =
      v i * (gaussDerivEntry t ht (Fin.cons i ι) (x - y) * g y) by intro y; ring]
    exact integral_const_mul _ _
  · intro i _
    have hi := testNorm_convolution_integrable r hr
      (gaussDeriv_memLp_iterated t ht (Fin.cons i ι) _
        (Real.HolderConjugate.conjExponent hr).symm.pos) hg x
    simpa only [gaussDerivEntry, mul_comm, mul_left_comm, mul_assoc] using hi.const_mul (v i)

theorem testNorm_gaussDeriv_contDiff {d j : ℕ} (r : ℝ) (hr : 1 < r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, gaussDerivEntry t ht ι (x - y) * g y) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing j with
  | zero =>
    have hd : Differentiable ℝ (fun x => ∫ y, gaussDerivEntry t ht ι (x - y) * g y) :=
      fun x => (testNorm_gaussDeriv_hasFDerivAt r hr g hg t ht ι x).differentiableAt
    exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (testNorm_gaussDeriv_hasFDerivAt r hr g hg t ht ι x).differentiableAt,
      by simp, fun v => ?_⟩
    have heq : (fun x => fderiv ℝ (fun x => ∫ y, gaussDerivEntry t ht ι (x - y) * g y) x v) =
        fun x => ∑ i, v i * ∫ y, gaussDerivEntry t ht (Fin.cons i ι) (x - y) * g y := by
      funext x
      exact testNorm_gaussDeriv_fderiv_apply r hr g hg t ht ι x v
    rw [heq]
    apply ContDiff.sum
    intro i _
    have hc : ContDiff ℝ (n : WithTop ℕ∞)
        (fun x => ∫ y, gaussDerivEntry t ht (Fin.cons i ι) (x - y) * g y) := ih (Fin.cons i ι)
    exact contDiff_const.mul hc

theorem testNorm_gaussian_contDiff {d : ℕ} (r : ℝ) (hr : 1 < r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) := by
  simpa only [gaussDerivEntry, iteratedFDeriv_zero_apply] using
    testNorm_gaussDeriv_contDiff r hr g hg t ht (Fin.elim0 : Fin 0 → Fin d)

theorem testNorm_gaussian_iteratedFDeriv {d j : ℕ} (r : ℝ) (hr : 1 < r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) (x : Vec d) :
    iteratedFDeriv ℝ j (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) x
      (fun k => basisVec (ι k)) = ∫ y, gaussDerivEntry t ht ι (x - y) * g y := by
  induction j generalizing x with
  | zero => simp only [gaussDerivEntry, iteratedFDeriv_zero_apply]
  | succ j ih =>
    have hd := (testNorm_gaussian_contDiff r hr g hg t ht).differentiable_iteratedFDeriv
      (m := j) (by exact_mod_cast (ENat.natCast_lt_top j))
    rw [hd.differentiableAt.iteratedFDeriv_succ_apply_left']
    have heq : (fun x => iteratedFDeriv ℝ j
        (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) x
          (Fin.tail fun k => basisVec (ι k))) =
        fun x => ∫ y, gaussDerivEntry t ht (Fin.tail ι) (x - y) * g y := by
      funext x
      exact ih (Fin.tail ι) x
    rw [heq, testNorm_gaussDeriv_fderiv_apply r hr g hg]
    simp only [basisVec, Pi.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Fin.cons_self_tail]

end CoarseDeGiorgi.NegSobolev
