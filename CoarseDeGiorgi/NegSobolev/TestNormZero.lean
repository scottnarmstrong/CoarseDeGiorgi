module

public import CoarseDeGiorgi.NegSobolev.GaussDerivLp
public import CoarseDeGiorgi.NegSobolev.GaussianContraction
public import CoarseDeGiorgi.Statements.SobolevNormZero
public import Mathlib.Analysis.Convolution

/-! Gaussian convolution for arbitrary finite-exponent input, including the
order-zero Sobolev test-function estimate. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Convolution

namespace CoarseDeGiorgi.NegSobolev

/-- Convolution with a Gaussian is bounded for every finite exponent above one. -/
theorem testNorm_gaussian_bounded {d : ℕ} (r : ℝ) (hr : 1 < r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) :
    ∃ B : ℝ, ∀ x : Vec d, |∫ y, gaussianKernel t ht (x - y) * g y| ≤ B := by
  let q : ℝ := r / (r - 1)
  have hconj : r.HolderConjugate q := Real.HolderConjugate.conjExponent hr
  let : (ENNReal.ofReal q).HolderConjugate (ENNReal.ofReal r) := hconj.symm.ennrealOfReal
  have hK := gaussDeriv_memLp (d := d) t ht q hconj.symm.pos
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let B : ℝ≥0∞ := ‖L‖ₑ * eLpNorm (gaussianKernel (d := d) t ht) (ENNReal.ofReal q) volume *
    eLpNorm g (ENNReal.ofReal r) volume
  have hB : B < ⊤ := by
    dsimp only [B]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by finiteness) hK.eLpNorm_lt_top) hg.eLpNorm_lt_top
  refine ⟨B.toReal, fun x => ?_⟩
  have h := enorm_convolution_le (p := ENNReal.ofReal q) (q := ENNReal.ofReal r) L hK.aestronglyMeasurable hg.aestronglyMeasurable x
  rw [convolution_eq_swap] at h
  change ‖∫ y, gaussianKernel t ht (x - y) * g y‖ₑ ≤ B at h
  have hh := ENNReal.toReal_mono hB.ne h
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using hh

/-- The full-space Gaussian convolution remains in the input Lebesgue class. -/
theorem testNorm_gaussian_memLp {d : ℕ} (r : ℝ) (hr : 1 ≤ r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) :
    MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) (ENNReal.ofReal r) volume := by
  have htconv := eLpNorm_gaussianKernel_smul_le_ae t ht g hg.aestronglyMeasurable r hr
  have heq' : (fun x => ∫ y, gaussianKernel t ht y • g (x - y)) =
      fun x => ∫ y, gaussianKernel t ht (x - y) * g y := by
    funext x
    exact convolution_eq_swap (L := ContinuousLinearMap.lsmul ℝ ℝ)
  rw [heq'] at htconv
  exact htconv.trans_lt hg.eLpNorm_lt_top

/-- At order zero the Sobolev norm is contracted by Gaussian averaging, on
any open carrier, with constant one independent of the function and time. -/
theorem testNorm_gaussian_order_zero {d : ℕ} (r : ℝ) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : Set (Vec d)) (hU : IsOpen U)
      (g : Vec d → ℝ), MemLp g (ENNReal.ofReal r) volume →
      ∀ (t : ℝ) (ht : 0 < t),
      MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) ⊤ (volume.restrict U) ∧
        sobolevNorm U hU 0 r le_rfl hr.le
          (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) ≤
            ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal r) volume := by
  refine ⟨1, zero_lt_one, fun U hU g hg t ht => ?_⟩
  have hc := testNorm_gaussian_memLp r hr.le g hg t ht
  obtain ⟨B, hB⟩ := testNorm_gaussian_bounded r hr g hg t ht
  constructor
  · exact memLp_top_of_bound (hc.aestronglyMeasurable.mono_measure Measure.restrict_le_self) B
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  · rw [CoarseDeGiorgi.sobolevNorm_zero hU hr.le, ENNReal.ofReal_one, one_mul]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    have htconv := eLpNorm_gaussianKernel_smul_le_ae t ht g hg.aestronglyMeasurable r hr.le
    have heq : (fun x => ∫ y, gaussianKernel t ht y • g (x - y)) =
        fun x => ∫ y, gaussianKernel t ht (x - y) * g y := by
      funext x
      exact convolution_eq_swap (L := ContinuousLinearMap.lsmul ℝ ℝ)
    rwa [heq] at htconv

end CoarseDeGiorgi.NegSobolev
