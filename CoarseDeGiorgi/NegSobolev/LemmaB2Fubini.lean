module

public import CoarseDeGiorgi.Statements.GaussianKernel
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Fubini for an even integrable kernel and bounded dual tests. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- The two-variable pairing is integrable for an integrable kernel and bounded test. -/
theorem lemmaB2_pairing_integrable {d : ℕ} {K f g : Vec d → ℝ}
    (hK : Integrable K volume) (hf : Integrable f volume) (hg : MemLp g ⊤ volume) :
    Integrable (fun z : Vec d × Vec d => (K (z.1 - z.2) * f z.2) * g z.1)
      (volume.prod volume) := by
  have hbase := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hK
  have hgt : eLpNormEssSup g volume < ⊤ := by
    rw [← eLpNorm_exponent_top hg.aestronglyMeasurable]
    exact hg.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hgt
  have hbound : ∀ᵐ z : Vec d × Vec d ∂(volume.prod volume), ‖g z.1‖ ≤ (C : ℝ) := by
    exact (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure (Vec d))).ae hC).mono (fun z hz => hz)
  have h := hbase.mul_bdd hg.aestronglyMeasurable.comp_fst hbound
  simpa only [ContinuousLinearMap.mul_apply', mul_comm (f _)] using h

/-- Evenness moves a convolution across the scalar integral pairing. -/
theorem lemmaB2_even_kernel_pairing {d : ℕ} {K f g : Vec d → ℝ}
    (hK : Integrable K volume) (heven : ∀ x, K (-x) = K x)
    (hf : Integrable f volume) (hg : MemLp g ⊤ volume) :
    (∫ x, (∫ y, K (x - y) * f y ∂volume) * g x ∂volume) =
      ∫ y, f y * (∫ x, K (y - x) * g x ∂volume) ∂volume := by
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap (lemmaB2_pairing_integrable hK hf hg)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hs : K (y - x) = K (x - y) := by
    rw [← neg_sub x y, heven]
  rw [hs]
  ring

/-- For zero extension the right side is the integral over the original open set. -/
theorem lemmaB2_even_kernel_pairing_on {d : ℕ} {K f g : Vec d → ℝ}
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (hK : Integrable K volume) (heven : ∀ x, K (-x) = K x)
    (hf : Integrable f (volume.restrict U)) (hg : MemLp g ⊤ volume) :
    (∫ x, (∫ y, K (x - y) * U.indicator f y ∂volume) * g x ∂volume) =
      ∫ y in U, f y * (∫ x, K (y - x) * g x ∂volume) ∂volume := by
  rw [lemmaB2_even_kernel_pairing hK heven ((integrable_indicator_iff hU).mpr hf) hg]
  rw [← integral_indicator hU]
  congr 1
  ext y
  by_cases hy : y ∈ U
  · simp only [Set.indicator_of_mem hy]
  · simp only [Set.indicator_of_notMem hy, zero_mul]

/-- The Gaussian has the evenness needed in the preceding identity. -/
theorem lemmaB2_gaussian_even {d : ℕ} (t : ℝ) (ht : 0 < t) (x : Vec d) :
    gaussianKernel t ht (-x) = gaussianKernel t ht x := by
  simp only [gaussianKernel, vecNormSq, vecDot, Pi.neg_apply, neg_mul_neg]

/-- The exact Gaussian Fubini identity, with its analytic integrability condition explicit. -/
theorem lemmaB2_gaussian_pairing_on {d : ℕ} (t : ℝ) (ht : 0 < t)
    {f g : Vec d → ℝ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (hK : Integrable (gaussianKernel (d := d) t ht) volume)
    (hf : Integrable f (volume.restrict U)) (hg : MemLp g ⊤ volume) :
    (∫ x, (∫ y, gaussianKernel t ht (x - y) * U.indicator f y ∂volume) * g x ∂volume) =
      ∫ y in U, f y * (∫ x, gaussianKernel t ht (y - x) * g x ∂volume) ∂volume :=
  lemmaB2_even_kernel_pairing_on hU hK (lemmaB2_gaussian_even t ht) hf hg

end CoarseDeGiorgi.NegSobolev
