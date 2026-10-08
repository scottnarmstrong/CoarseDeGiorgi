import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace CoarseDeGiorgi.Selection

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section


/-- Chebyshev for a powered nonnegative quantity, including infinite function values. -/
theorem measure_bad_le_of_power_integral {μ : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) {r : ℝ} (hr : 0 < r) {T B : ℝ≥0∞}
    (hT : T ≠ 0) (hTtop : T ≠ ⊤) (hB : ∫⁻ τ, (f τ) ^ r ∂μ ≤ B) :
    μ {τ | T < f τ} ≤ B / T ^ r := by
  have hpow : Measurable (fun τ => (f τ) ^ r) := hf.pow_const r
  calc
    μ {τ | T < f τ} ≤ μ {τ | T ^ r ≤ (f τ) ^ r} := measure_mono (by
      intro τ hτ
      exact (ENNReal.rpow_le_rpow_iff hr).mpr hτ.le)
    _ ≤ (∫⁻ τ, (f τ) ^ r ∂μ) / T ^ r :=
      meas_ge_le_lintegral_div hpow.aemeasurable
        (fun h => hT ((ENNReal.rpow_eq_zero_iff_of_pos hr).mp h))
        (ENNReal.rpow_ne_top_of_nonneg hr.le hTtop)
    _ ≤ B / T ^ r := by gcongr

/-- A zero controlling integral contributes no exceptional radii. -/
theorem measure_bad_zero_of_power_integral_zero {μ : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) {r : ℝ} (hr : 0 < r) (hzero : ∫⁻ τ, (f τ) ^ r ∂μ = 0) :
    μ {τ | 0 < f τ} = 0 := by
  have h := (lintegral_eq_zero_iff (hf.pow_const r)).mp hzero
  have hz : ∀ᵐ τ ∂μ, ¬0 < f τ := by
    filter_upwards [h] with τ hτ
    have : f τ = 0 := (ENNReal.rpow_eq_zero_iff_of_pos hr).mp hτ
    simp [this]
  simpa only [ae_iff, not_not] using hz

/-- The interval of radii from which the surface is selected. -/
def selectionInterval (ρ R : ℝ) : Set ℝ := Ioo (ρ + (R - ρ) / 4) (ρ + (R - ρ) / 2)

theorem volume_selectionInterval (ρ R : ℝ) :
    volume (selectionInterval ρ R) = ENNReal.ofReal ((R - ρ) / 4) := by
  rw [selectionInterval, Real.volume_Ioo]
  congr 1
  ring

/-- Chebyshev at a normalized threshold, with zero and infinite controls dispatched.
The exceptional measure is `1/K` whenever the powered integral is at most `B^r`. -/
theorem normalized_bad_set_bound {μ : Measure ℝ} {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) {r : ℝ} (hr : 0 < r) {K B : ℝ≥0∞}
    (hK0 : K ≠ 0) (hKtop : K ≠ ⊤) (hB : ∫⁻ τ, (f τ) ^ r ∂μ ≤ B ^ r) :
    μ {τ | K ^ (1 / r) * B < f τ} ≤ K⁻¹ := by
  have hroot0 : K ^ (1 / r) ≠ 0 :=
    fun h => hK0 ((ENNReal.rpow_eq_zero_iff_of_pos (one_div_pos.mpr hr)).mp h)
  by_cases hB0 : B = 0
  · subst B
    have hz : ∫⁻ τ, (f τ) ^ r ∂μ = 0 := by
      simpa only [ENNReal.zero_rpow_of_pos hr, nonpos_iff_eq_zero] using hB
    rw [mul_zero, measure_bad_zero_of_power_integral_zero hf hr hz]
    exact zero_le
  by_cases hBtop : B = ⊤
  · subst B
    rw [ENNReal.mul_top hroot0]
    have he : {τ | (⊤ : ℝ≥0∞) < f τ} = ∅ := by ext τ; simp
    rw [he, measure_empty]
    exact zero_le
  have hT0 : K ^ (1 / r) * B ≠ 0 := mul_ne_zero hroot0 hB0
  have hTtop : K ^ (1 / r) * B ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hKtop)
      (lt_top_iff_ne_top.mpr hBtop)).ne
  apply (measure_bad_le_of_power_integral hf hr hT0 hTtop hB).trans_eq
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hr.ne', ENNReal.rpow_one]
  have hpow0 : B ^ r ≠ 0 := fun h => hB0 ((ENNReal.rpow_eq_zero_iff_of_pos hr).mp h)
  have hpowtop : B ^ r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hr.le hBtop
  rw [mul_comm K (B ^ r)]
  simpa only [mul_one, one_div] using ENNReal.mul_div_mul_left (1 : ℝ≥0∞) K hpow0 hpowtop

/-- Localized form: all bad-set budgets are measured only inside `J`. -/
theorem exists_common_radius_of_local_bad_set_bounds {ι : Type*} [Fintype ι]
    {J : Set ℝ} {Good : ℝ → Prop} {f : ι → ℝ → ℝ≥0∞} {threshold : ι → ℝ≥0∞}
    {budget : ι → ℝ≥0∞}
    (hgood : ∀ᵐ τ ∂volume.restrict J, Good τ)
    (hbad : ∀ i, (volume.restrict J) {τ | threshold i < f i τ} ≤ budget i)
    (hsmall : ∑ i, budget i < volume J) :
    ∃ τ ∈ J, Good τ ∧ ∀ i, f i τ ≤ threshold i := by
  classical
  by_contra! hnone
  have hnull : (volume.restrict J) {τ | ¬Good τ} = 0 := by simpa only [ae_iff] using hgood
  have hsub : J ⊆ (⋃ i, {τ | threshold i < f i τ}) ∪ {τ | ¬Good τ} := by
    intro τ hτ
    by_cases hg : Good τ
    · obtain ⟨i, hi⟩ := hnone τ hτ hg
      exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
    · exact Or.inr hg
  have hle : volume J ≤ ∑ i, budget i := by
    calc
      volume J = (volume.restrict J) J := (Measure.restrict_apply_self _ _).symm
      _ ≤ (volume.restrict J) ((⋃ i, {τ | threshold i < f i τ}) ∪ {τ | ¬Good τ}) := measure_mono hsub
      _ ≤ (volume.restrict J) (⋃ i, {τ | threshold i < f i τ}) + (volume.restrict J) {τ | ¬Good τ} := measure_union_le _ _
      _ ≤ (∑ i, (volume.restrict J) {τ | threshold i < f i τ}) + 0 := by
        rw [hnull]
        simpa only [add_zero] using measure_iUnion_fintype_le (volume.restrict J)
          (fun i => {τ | threshold i < f i τ})
      _ ≤ ∑ i, budget i := by simp only [add_zero]; exact Finset.sum_le_sum (fun i _ => hbad i)
  exact (not_lt_of_ge hle) hsmall


end

end CoarseDeGiorgi.Selection
