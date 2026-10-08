import CoarseDeGiorgi.NegSobolev.GaussianBasic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Finite-exponent integrability of the Gaussian kernel. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- Every positive real power of the Gaussian is integrable on the full space. -/
theorem gaussDeriv_integrable_rpow {d : ℕ} (t : ℝ) (ht : 0 < t)
    (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : Vec d => gaussianKernel t ht x ^ r) volume := by
  have heq : (fun x : Vec d => gaussianKernel t ht x ^ r) =
      fun x => ((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) ^ r *
        ∏ i : Fin d, Real.exp (-(r / (4 * t)) * x i ^ 2) := by
    funext x
    unfold gaussianKernel
    rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _),
      ← Real.exp_mul, ← Real.exp_sum]
    congr 2
    unfold vecNormSq vecDot
    simp only [← pow_two, ← Finset.mul_sum]
    ring
  rw [heq]
  exact (Integrable.fintype_prod (fun _ =>
    integrable_exp_neg_mul_sq (by positivity : 0 < r / (4 * t)))).const_mul _

/-- The Gaussian belongs to every positive finite Lebesgue exponent. -/
theorem gaussDeriv_memLp {d : ℕ} (t : ℝ) (ht : 0 < t)
    (r : ℝ) (hr : 0 < r) : MemLp (gaussianKernel (d := d) t ht) (ENNReal.ofReal r) volume := by
  apply (integrable_norm_rpow_iff
    (continuous_gaussianKernel t ht).aestronglyMeasurable
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_ofReal hr.le]
  have hn (x : Vec d) : ‖gaussianKernel t ht x‖ = gaussianKernel t ht x :=
    Real.norm_of_nonneg (gaussianKernel_nonneg t ht x)
  simp_rw [hn]
  exact gaussDeriv_integrable_rpow t ht r hr

end CoarseDeGiorgi.NegSobolev
