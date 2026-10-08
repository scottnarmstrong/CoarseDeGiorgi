import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace CoarseDeGiorgi.Endpoint.Potential

open MeasureTheory Set
open scoped ENNReal

/-- The elementary integral `∫_{0 < t, t ≤ T} t^(η-1) = T^η / η`, in extended reals. -/
theorem lintegral_levelset_rpow {η : ℝ} (hη : 0 < η) (T : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), (if ENNReal.ofReal t ≤ T then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (t ^ (η - 1)) ≤ ENNReal.ofReal η⁻¹ * T ^ η := by
  by_cases hT : T = ⊤
  · subst hT
    rw [ENNReal.top_rpow_of_pos hη, ENNReal.mul_top (by simpa using hη)]
    exact le_top
  have hT' : ENNReal.ofReal T.toReal = T := ENNReal.ofReal_toReal hT
  have h1 : ∫⁻ t in Ioi (0 : ℝ), (if ENNReal.ofReal t ≤ T then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (t ^ (η - 1)) =
      ∫⁻ t in Ioc (0 : ℝ) T.toReal, ENNReal.ofReal (t ^ (η - 1)) := by
    have hc : ∀ t ∈ Ioi (0 : ℝ), (if ENNReal.ofReal t ≤ T then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (t ^ (η - 1)) =
        (Ioc (0 : ℝ) T.toReal).indicator (fun t => ENNReal.ofReal (t ^ (η - 1))) t := by
      intro t ht
      have ht0 : 0 < t := ht
      by_cases hle : t ≤ T.toReal
      · have : ENNReal.ofReal t ≤ T := (ENNReal.ofReal_le_iff_le_toReal hT).2 hle
        simp [this, ht0, hle]
      · have : ¬ ENNReal.ofReal t ≤ T := fun h => hle ((ENNReal.ofReal_le_iff_le_toReal hT).1 h)
        simp [this, hle]
    rw [setLIntegral_congr_fun measurableSet_Ioi hc, lintegral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioi]
    · simp
  rw [h1]
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (η - 1)) volume 0 T.toReal :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) T.toReal)] fun t : ℝ => t ^ (η - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have hT0 : 0 ≤ T.toReal := ENNReal.toReal_nonneg
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 hint) hnn,
    ← intervalIntegral.integral_of_le hT0, integral_rpow (Or.inl (by linarith))]
  have : η - 1 + 1 = η := by ring
  rw [this, Real.zero_rpow hη.ne', sub_zero]
  rw [show (T.toReal ^ η / η) = η⁻¹ * T.toReal ^ η by ring,
    ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hT0 hη.le, hT']

/-- Layer-cake bound from a covering of the level sets by weighted pieces. -/
theorem lintegral_rpow_le_tsum {α : Type*} [MeasurableSpace α] (μ : Measure α) {v : α → ℝ}
    (hv : AEMeasurable v μ) {η : ℝ} (hη : 0 < η) (w T : ℕ → ℝ≥0∞)
    (hlevel : ∀ K : ℝ, 0 < K →
      μ {x | K < |v x|} ≤ ∑' N, w N * (if ENNReal.ofReal K ≤ T N then 1 else 0)) :
    ∫⁻ x, ENNReal.ofReal (|v x| ^ η) ∂μ ≤ ∑' N, w N * T N ^ η := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (Filter.Eventually.of_forall fun x => abs_nonneg (v x))
    (continuous_abs.measurable.comp_aemeasurable hv) hη]
  have hm1 : ∀ N : ℕ, Measurable fun t : ℝ => (if ENNReal.ofReal t ≤ T N then (1 : ℝ≥0∞) else 0) := by
    intro N
    have hs : MeasurableSet {t : ℝ | ENNReal.ofReal t ≤ T N} :=
      measurableSet_le ENNReal.measurable_ofReal measurable_const
    exact Measurable.ite hs measurable_const measurable_const
  have hm2 : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (η - 1)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hm3 : ∀ N : ℕ, Measurable fun t : ℝ => (w N * (if ENNReal.ofReal t ≤ T N then (1 : ℝ≥0∞)
      else 0)) * ENNReal.ofReal (t ^ (η - 1)) := fun N =>
    ((hm1 N).const_mul (w N)).mul hm2
  calc ENNReal.ofReal η * ∫⁻ t in Ioi (0 : ℝ), μ {x | t < |v x|} * ENNReal.ofReal (t ^ (η - 1))
      ≤ ENNReal.ofReal η * ∫⁻ t in Ioi (0 : ℝ), (∑' N, w N *
          (if ENNReal.ofReal t ≤ T N then (1 : ℝ≥0∞) else 0)) * ENNReal.ofReal (t ^ (η - 1)) := by
        refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
        filter_upwards [ae_restrict_mem (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
        exact mul_le_mul' (hlevel t ht) le_rfl
    _ = ENNReal.ofReal η * ∑' N, w N * ∫⁻ t in Ioi (0 : ℝ),
          (if ENNReal.ofReal t ≤ T N then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (t ^ (η - 1)) := by
        congr 1
        simp_rw [← ENNReal.tsum_mul_right]
        rw [lintegral_tsum (fun N => (hm3 N).aemeasurable)]
        congr 1
        funext N
        simp_rw [mul_assoc]
        exact lintegral_const_mul _ ((hm1 N).mul hm2)
    _ ≤ ENNReal.ofReal η * ∑' N, w N * (ENNReal.ofReal η⁻¹ * T N ^ η) := by
        gcongr with N
        exact lintegral_levelset_rpow hη (T N)
    _ = ∑' N, w N * T N ^ η := by
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext N
        rw [← mul_assoc, mul_comm (ENNReal.ofReal η) (w N), mul_assoc, ← mul_assoc (ENNReal.ofReal η),
          ← ENNReal.ofReal_mul hη.le, mul_inv_cancel₀ hη.ne', ENNReal.ofReal_one, one_mul]

end CoarseDeGiorgi.Endpoint.Potential
