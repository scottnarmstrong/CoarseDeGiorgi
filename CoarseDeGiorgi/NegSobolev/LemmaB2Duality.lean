import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Scalar duality with bounded tests for nonnegative bounded functions. -/

open MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- An integrable bounded function belongs to every finite `Lᵖ`, `p ≥ 1`. -/
theorem lemmaB2_memLp_of_integrable_bounded {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (hf : Integrable f μ) (hf_top : MemLp f ⊤ μ)
    (p : ℝ) (hp : 1 < p) : MemLp f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have ht : eLpNormEssSup f μ < ⊤ := by
    rw [← eLpNorm_exponent_top hf_top.aestronglyMeasurable]
    exact hf_top.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp ht
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp0.le]
  refine Integrable.mono' (hf.norm.const_mul ((C : ℝ) ^ (p - 1)))
    (hf.aestronglyMeasurable.norm.aemeasurable.pow_const p).aestronglyMeasurable ?_
  filter_upwards [hC] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc
    _ = ‖f x‖ ^ (p - 1) * ‖f x‖ := by
      rw [← Real.rpow_add_one' (norm_nonneg _) (by linarith : p - 1 + 1 ≠ 0)]
      congr 1
      ring
    _ ≤ (C : ℝ) ^ (p - 1) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) hx hp1.le) (norm_nonneg _)

/-- The power of a finite `Lᵖ` norm is the integral of the power. -/
theorem lemmaB2_norm_power_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {p : ℝ} (hp : 0 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ) ^ p = ENNReal.ofReal (∫ x, ‖f x‖ ^ p ∂μ) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ p ∂μ := integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hI _) hp.le,
    ← Real.rpow_mul hI, inv_mul_cancel₀ hp.ne', Real.rpow_one]

/-- Bounded tests recover the `Lᵖ` norm of a nonnegative function in `Lᵖ ∩ L∞`.
The test is `|f|^(p-1)`, which is bounded because `f` is bounded. -/
theorem lemmaB2_nonneg_duality {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} (p : ℝ) (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hf_top : MemLp f ⊤ μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (K : ℝ≥0∞)
    (htest : ∀ g : X → ℝ, MemLp g (ENNReal.ofReal (p / (p - 1))) μ → MemLp g ⊤ μ →
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ K * eLpNorm g (ENNReal.ofReal (p / (p - 1))) μ) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ K := by
  have hp1 : 0 < p - 1 := sub_pos.mpr hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hexp : ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (div_nonneg hp0.le hp1.le), div_mul_cancel₀ p hp1.ne']
  let g : X → ℝ := fun x => ‖f x‖ ^ (p - 1)
  have hgn : eLpNorm g (ENNReal.ofReal (p / (p - 1))) μ =
      eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) := by
    rw [eLpNorm_norm_rpow f hf.aestronglyMeasurable hp1, hexp]
  have hg : MemLp g (ENNReal.ofReal (p / (p - 1))) μ := by
    rw [memLp_iff]
    rw [hgn]
    exact ENNReal.rpow_lt_top_of_nonneg hp1.le hf.eLpNorm_ne_top
  have hg_top : MemLp g ⊤ μ := by
    rw [memLp_iff]
    rw [eLpNorm_norm_rpow f hf_top.aestronglyMeasurable hp1,
      ENNReal.top_mul (ne_of_gt (ENNReal.ofReal_pos.mpr hp1))]
    exact ENNReal.rpow_lt_top_of_nonneg hp1.le hf_top.eLpNorm_ne_top
  have hpair : ENNReal.ofReal |∫ x, f x * g x ∂μ| = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
    have hi : (∫ x, f x * g x ∂μ) = ∫ x, ‖f x‖ ^ p ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf0] with x hx
      simp only [g, Real.norm_eq_abs, abs_of_nonneg hx]
      rw [← Real.rpow_one_add' hx (by linarith : 1 + (p - 1) ≠ 0)]
      congr 1
      ring
    rw [hi, abs_of_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
    exact (lemmaB2_norm_power_integral hp0 hf).symm
  have ht := htest g hg hg_top
  rw [hpair, hgn] at ht
  by_cases hz : eLpNorm f (ENNReal.ofReal p) μ = 0
  · rw [hz]
    exact bot_le
  have hD0 : eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hz) hp1.le)
  have hDt : eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp1.le hf.eLpNorm_ne_top
  have heq : eLpNorm f (ENNReal.ofReal p) μ ^ p =
      eLpNorm f (ENNReal.ofReal p) μ * eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1) := by
    calc
      _ = eLpNorm f (ENNReal.ofReal p) μ ^ (1 + (p - 1)) := by congr 1; ring
      _ = _ := by rw [ENNReal.rpow_add _ _ hz hf.eLpNorm_ne_top, ENNReal.rpow_one]
  rw [heq] at ht
  have hcancel := mul_le_mul_left ht (eLpNorm f (ENNReal.ofReal p) μ ^ (p - 1))⁻¹
  simpa only [mul_assoc, ENNReal.mul_inv_cancel hD0 hDt, mul_one] using hcancel

end CoarseDeGiorgi.NegSobolev
