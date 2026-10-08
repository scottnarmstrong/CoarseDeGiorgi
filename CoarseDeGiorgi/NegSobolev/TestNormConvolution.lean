import CoarseDeGiorgi.NegSobolev.GaussDerivLocal
import CoarseDeGiorgi.NegSobolev.TestNormZero

/-! Integrability and Lebesgue bounds for kernels dominated by a Gaussian. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Convolution

namespace CoarseDeGiorgi.NegSobolev

theorem testNorm_convolution_integrable {d : ℕ} (r : ℝ) (hr : 1 < r)
    {K g : Vec d → ℝ} (hK : MemLp K (ENNReal.ofReal (r / (r - 1))) volume)
    (hg : MemLp g (ENNReal.ofReal r) volume) (x : Vec d) :
    Integrable (fun y => K (x - y) * g y) volume := by
  have hc := Real.HolderConjugate.conjExponent hr
  let : (ENNReal.ofReal (r / (r - 1))).HolderConjugate (ENNReal.ofReal r) := hc.symm.ennrealOfReal
  exact (convolutionExistsAt_iff_integrable_swap
    (L := ContinuousLinearMap.lsmul ℝ ℝ)).mp
    (ConvolutionExists.of_memLp_memLp (ContinuousLinearMap.lsmul ℝ ℝ) hK hg x)

theorem testNorm_gaussian_mul_integrable {d : ℕ} (r : ℝ) (hr : 1 < r)
    {g : Vec d → ℝ} (hg : MemLp g (ENNReal.ofReal r) volume)
    (s : ℝ) (hs : 0 < s) (x : Vec d) :
    Integrable (fun y => gaussianKernel s hs (x - y) * |g y|) volume := by
  have hc := Real.HolderConjugate.conjExponent hr
  exact testNorm_convolution_integrable r hr
    (gaussDeriv_memLp s hs _ hc.symm.pos) hg.norm x

theorem testNorm_convolution_le_gaussian {d : ℕ} (r : ℝ) (hr : 1 < r)
    {K g : Vec d → ℝ} (hK : AEStronglyMeasurable K volume)
    (hg : MemLp g (ENNReal.ofReal r) volume) (A s : ℝ) (_hA : 0 ≤ A) (hs : 0 < s)
    (hbound : ∀ x, |K x| ≤ A * gaussianKernel s hs x) (x : Vec d) :
    |∫ y, K (x - y) * g y| ≤
      A * ∫ y, gaussianKernel s hs (x - y) * |g y| := by
  have hgi := testNorm_gaussian_mul_integrable r hr hg s hs x
  have hc := Real.HolderConjugate.conjExponent hr
  have hKl : MemLp K (ENNReal.ofReal (r / (r - 1))) volume :=
    ((gaussDeriv_memLp s hs _ hc.symm.pos).const_smul A).mono' hK
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul] using hbound z)
  have hKi := testNorm_convolution_integrable r hr hKl hg x
  calc
    _ ≤ ∫ y, |K (x - y) * g y| := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => K (x - y) * g y)
    _ ≤ ∫ y, A * (gaussianKernel s hs (x - y) * |g y|) :=
      integral_mono hKi.norm (hgi.const_mul A) fun y => by
        rw [abs_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem testNorm_convolution_eLpNorm_le_gaussian {d : ℕ} (r : ℝ) (hr : 1 < r)
    {K g : Vec d → ℝ} (hK : AEStronglyMeasurable K volume)
    (hg : MemLp g (ENNReal.ofReal r) volume) (A s : ℝ) (hA : 0 ≤ A) (hs : 0 < s)
    (hbound : ∀ x, |K x| ≤ A * gaussianKernel s hs x) :
    eLpNorm (fun x => ∫ y, K (x - y) * g y) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal r) volume := by
  let G := fun x => ∫ y, gaussianKernel s hs (x - y) * |g y|
  have hG := testNorm_gaussian_memLp r hr.le (fun y => |g y|) hg.norm s hs
  have hG0 (x) : 0 ≤ G x := integral_nonneg fun y =>
    mul_nonneg (gaussianKernel_nonneg _ _ _) (abs_nonneg _)
  have hm : AEStronglyMeasurable (fun x => ∫ y, K (x - y) * g y) volume := by
    have hh := hK.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hg.aestronglyMeasurable
    have heq : (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
        (fun x => ∫ y, K (x - y) * g y) := by
      funext x
      exact convolution_eq_swap (L := ContinuousLinearMap.lsmul ℝ ℝ)
    rwa [heq] at hh
  have hle : eLpNorm (fun x => ∫ y, K (x - y) * g y) (ENNReal.ofReal r) volume ≤
      eLpNorm (A • G) (ENNReal.ofReal r) volume := by
    apply eLpNorm_mono_ae hm
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul,
        abs_of_nonneg (mul_nonneg hA (hG0 x))] using
        testNorm_convolution_le_gaussian r hr hK hg A s hA hs hbound x
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hA] at hle
  refine hle.trans (mul_le_mul' le_rfl ?_)
  have hconv := eLpNorm_gaussianKernel_smul_le_ae s hs (fun y => |g y|)
    hg.norm.aestronglyMeasurable r hr.le
  have heq : (fun x => ∫ y, gaussianKernel s hs y • |g (x - y)|) = G := by
    funext x
    exact convolution_eq_swap (f := gaussianKernel s hs) (g := fun y => |g y|)
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
  rw [heq] at hconv
  simpa only [← Real.norm_eq_abs, eLpNorm_norm g hg.aestronglyMeasurable] using hconv

theorem testNorm_gaussDeriv_eLpNorm_bound (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (_hr : 1 < r) (g : Vec d → ℝ),
      MemLp g (ENNReal.ofReal r) volume → ∀ (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d),
      eLpNorm (fun x => ∫ y, gaussDerivEntry t ht ι (x - y) * g y)
        (ENNReal.ofReal r) volume ≤
          ENNReal.ofReal (C * t ^ (-((j : ℝ) / 2))) * eLpNorm g (ENNReal.ofReal r) volume := by
  obtain ⟨C, hC, hbound⟩ := gaussDeriv_domination d j
  refine ⟨C, hC, fun r hr g hg t ht ι => ?_⟩
  exact testNorm_convolution_eLpNorm_le_gaussian r hr
    (gaussDerivEntry_contDiff t ht ι).continuous.aestronglyMeasurable hg
    _ _ (by positivity) (by positivity) (hbound t ht ι)

end CoarseDeGiorgi.NegSobolev
