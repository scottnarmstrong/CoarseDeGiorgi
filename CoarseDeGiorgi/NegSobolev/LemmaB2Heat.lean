import CoarseDeGiorgi.NegSobolev.LemmaB2Duality
import CoarseDeGiorgi.NegSobolev.LemmaB2Trace
import CoarseDeGiorgi.NegSobolev.LemmaB2Fubini
import CoarseDeGiorgi.NegSobolev.GaussianMatrix

/-! Integrability and trace domination of Gaussian matrix averages. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- Gaussian convolution of an `L¹` function is integrable and bounded. -/
theorem lemmaB2_scalar_heat_memLp {d : ℕ} (t : ℝ) (ht : 0 < t)
    {f : Vec d → ℝ} (hf : Integrable f volume) (p : ℝ) (hp : 1 < p) :
    MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * f y ∂volume) (ENNReal.ofReal p) volume ∧
      MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * f y ∂volume) ⊤ volume := by
  have hbase := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_gaussianKernel t ht)
  have hi : Integrable (fun x => ∫ y, gaussianKernel t ht (x - y) * f y ∂volume) volume := by
    simpa only [ContinuousLinearMap.mul_apply', mul_comm (f _)] using hbase.integral_prod_left
  have hb : MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * f y ∂volume) ⊤ volume := by
    apply memLp_top_of_bound hi.aestronglyMeasurable
      (((4 * Real.pi * t) ^ (-((d : ℝ) / 2))) * ∫ y, ‖f y‖ ∂volume)
    apply Filter.Eventually.of_forall
    intro x
    rw [← integral_const_mul]
    apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
    apply Filter.Eventually.of_forall
    intro y
    rw [norm_mul, Real.norm_of_nonneg (gaussianKernel_nonneg t ht (x - y))]
    exact mul_le_mul_of_nonneg_right (gaussianKernel_le_prefactor t ht (x - y)) (norm_nonneg _)
  exact ⟨lemmaB2_memLp_of_integrable_bounded hi hb p hp, hb⟩

/-- Entrywise integrability gives integrability of the scalar trace. -/
theorem lemmaB2_trace_integrable {d : ℕ} {μ : Measure (Vec d)} {b : Vec d → Mat d}
    (hb : ∀ i j, Integrable (fun x => b x i j) μ) :
    Integrable (fun x => (b x).trace) μ := by
  exact integrable_finsetSum _ (fun i _ => hb i i)

/-- The trace of the Gaussian average is the Gaussian average of the trace. -/
theorem lemmaB2_heat_trace {d : ℕ} (t : ℝ) (ht : 0 < t)
    (b : Vec d → Mat d) (hb : ∀ i j, Integrable (fun y => b y i j) volume) (x : Vec d) :
    (Matrix.of fun i j => ∫ y, gaussianKernel t ht (x - y) * b y i j ∂volume).trace =
      ∫ y, gaussianKernel t ht (x - y) * (b y).trace ∂volume := by
  simp only [Matrix.trace, Finset.mul_sum]
  exact (integral_finsetSum _ (fun i _ => integrable_gaussianKernel_mul t ht x (hb i i))).symm

/-- Positive semidefiniteness dominates the matrix heat norm by scalar trace heat. -/
theorem lemmaB2_matrix_heat_le_trace {d : ℕ} (t : ℝ) (ht : 0 < t)
    (b : Vec d → Mat d) (hb : ∀ i j, Integrable (fun y => b y i j) volume)
    (hpos : ∀ᵐ y ∂volume, (b y).PosSemidef) (p : ℝ) (hp : 1 < p) :
    eLpNorm (fun x => ‖Matrix.of fun i j => ∫ y, gaussianKernel t ht (x - y) * b y i j ∂volume‖)
      (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => ∫ y, gaussianKernel t ht (x - y) * (b y).trace ∂volume)
        (ENNReal.ofReal p) volume := by
  let : MeasurableSpace (Mat d) := MeasurableSpace.pi
  let : BorelSpace (Mat d) := inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have hmat : AEMeasurable (fun x => Matrix.of fun i j =>
      ∫ y, gaussianKernel t ht (x - y) * b y i j ∂volume) volume := by
    apply AEMeasurable.of_eval
    intro i
    apply AEMeasurable.of_eval
    intro j
    exact (lemmaB2_scalar_heat_memLp t ht (hb i j) p hp).1.aestronglyMeasurable.aemeasurable
  apply eLpNorm_mono_ae hmat.aestronglyMeasurable.norm
  apply Filter.Eventually.of_forall
  intro x
  have hx := gaussianKernel_convolution_posSemidef t ht b hb hpos x
  rw [Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (by rw [← lemmaB2_heat_trace t ht b hb x]; exact hx.trace_nonneg)]
  exact (lemmaB2_norm_le_trace hx).trans_eq (lemmaB2_heat_trace t ht b hb x)

/-- Gaussian dual tests turn a Sobolev test estimate into an `Lᵖ` trace heat estimate. -/
theorem lemmaB2_trace_heat_bound {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (t : ℝ) (ht : 0 < t) (β p : ℝ) (hβ : 0 ≤ β) (hp : 1 < p)
    (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (hpos : ∀ᵐ x ∂(volume.restrict U), (b x).PosSemidef)
    (M : ℝ) (hM : 0 < M)
    (htest : ∀ g : Vec d → ℝ, MemLp g (ENNReal.ofReal (p / (p - 1))) volume →
      MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ⊤ (volume.restrict U) ∧
        sobolevNorm U hU β (p / (p - 1)) hβ
          ((le_div_iff₀ (sub_pos.mpr hp)).mpr (by linarith))
          (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ≤
            ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) :
    eLpNorm (fun x => ∫ y, gaussianKernel t ht (x - y) * U.indicator (fun z => (b z).trace) y ∂volume)
      (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (d : ℝ) * ENNReal.ofReal M * negSobolevNorm U hU b hb β p hβ hp := by
  let f := U.indicator (fun z => (b z).trace)
  have hf : Integrable f volume := (integrable_indicator_iff hU.measurableSet).mpr
    (lemmaB2_trace_integrable hb)
  have hf0 : ∀ᵐ y ∂volume, 0 ≤ f y := by
    have hpos' := hpos
    rw [ae_restrict_iff' hU.measurableSet] at hpos'
    filter_upwards [hpos'] with y hy
    by_cases hyU : y ∈ U
    · dsimp only [f]
      rw [Set.indicator_of_mem hyU]
      exact (hy hyU).trace_nonneg
    · simp only [f, Set.indicator_of_notMem hyU, le_refl]
  obtain ⟨hheat, hheat_top⟩ := lemmaB2_scalar_heat_memLp t ht hf p hp
  apply lemmaB2_nonneg_duality p hp hheat hheat_top
  · apply Filter.Eventually.of_forall
    intro x
    apply integral_nonneg_of_ae
    filter_upwards [hf0] with y hy
    exact mul_nonneg (gaussianKernel_nonneg t ht (x - y)) hy
  · intro g hg hg_top
    by_cases hz : eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume = 0
    · have hqpos : 0 < p / (p - 1) := div_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hp)
      have hg0 := (eLpNorm_eq_zero_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hqpos))).mp hz
      have hzero : (fun x => (∫ y, gaussianKernel t ht (x - y) * f y ∂volume) * g x) =ᵐ[volume] 0 := by
        filter_upwards [hg0] with x hx
        simp only [hx, Pi.zero_apply, mul_zero]
      rw [integral_congr_ae hzero]
      simp only [Pi.zero_apply, integral_zero, abs_zero, ENNReal.ofReal_zero]
      exact bot_le
    have hgnpos : 0 < (eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume).toReal :=
      ENNReal.toReal_pos hz hg.eLpNorm_ne_top
    obtain ⟨hbounded, hnorm⟩ := htest g hg
    let A := M * (eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume).toReal
    have hA : 0 < A := mul_pos hM hgnpos
    have hAn : ENNReal.ofReal A = ENNReal.ofReal M * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume := by
      rw [ENNReal.ofReal_mul hM.le, ENNReal.ofReal_toReal hg.eLpNorm_ne_top]
    have hpair := lemmaB2_trace_pairing_le_of_bound hU b hb β p hβ hp
      (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) hbounded A hA
        (hnorm.trans_eq hAn.symm)
    rw [lemmaB2_gaussian_pairing_on t ht hU.measurableSet (integrable_gaussianKernel t ht)
      (lemmaB2_trace_integrable hb) hg_top]
    have hcomm : (∫ y in U, (b y).trace * (∫ x, gaussianKernel t ht (y - x) * g x ∂volume) ∂volume) =
        ∫ y in U, (∫ x, gaussianKernel t ht (y - x) * g x ∂volume) * (b y).trace ∂volume := by
      congr 1
      funext y
      exact mul_comm _ _
    rw [hcomm]
    exact hpair.trans_eq (by rw [hAn]; ac_rfl)

end CoarseDeGiorgi.NegSobolev
