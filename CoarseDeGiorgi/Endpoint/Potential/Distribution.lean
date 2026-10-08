import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace CoarseDeGiorgi.Endpoint.Potential

open MeasureTheory Filter Topology
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem lintegral_enorm_le_top {μ : Measure α} {h : α → ℝ} (hh : AEStronglyMeasurable h μ)
    (A : Set α) : ∫⁻ x in A, ‖h x‖ₑ ∂μ ≤ eLpNorm h ⊤ μ * μ A := by
  calc ∫⁻ x in A, ‖h x‖ₑ ∂μ ≤ ∫⁻ _ in A, eLpNorm h ⊤ μ ∂μ := by
        apply lintegral_mono_ae
        rw [eLpNorm_exponent_top hh]
        exact ae_restrict_of_ae ae_le_eLpNormEssSup
    _ = eLpNorm h ⊤ μ * μ A := by simp

theorem lintegral_enorm_le_lr {μ : Measure α} {h : α → ℝ} (hh : AEStronglyMeasurable h μ)
    {r : ℝ} (hr : 1 < r) (A : Set α) :
    ∫⁻ x in A, ‖h x‖ₑ ∂μ ≤ eLpNorm h (ENNReal.ofReal r) μ * μ A ^ (1 - 1 / r) := by
  have h1 : ∫⁻ x in A, ‖h x‖ₑ ∂μ = eLpNorm h 1 (μ.restrict A) :=
    (eLpNorm_one_eq_lintegral_enorm (hh.mono_measure Measure.restrict_le_self)).symm
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa using ENNReal.ofReal_le_ofReal hr.le
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict A) hle
    (hh.mono_measure Measure.restrict_le_self)
  rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_one, Measure.restrict_apply_univ] at h2
  rw [div_one] at h2
  rw [h1]
  refine h2.trans ?_
  gcongr
  exact Measure.restrict_le_self

/-- The level-set estimate: if `|f| ≥ K` on `A` and `f = ∑ vk` in `L^r`, then `K` is bounded by
the `L^∞` norms of the first `N` blocks plus `|A|^{-1/r}` times the `L^r` norms of the rest. -/
theorem distribution_bound (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} {vk : ℕ → α → ℝ} {r : ℝ} (hr : 1 < r)
    (hconv : Tendsto (fun M : ℕ => eLpNorm (fun x => f x - ∑ k ∈ Finset.Icc 1 M, vk k x)
      (ENNReal.ofReal r) μ) atTop (𝓝 0))
    (hvm : ∀ k, 1 ≤ k → AEStronglyMeasurable (vk k) μ)
    (hfm : AEStronglyMeasurable f μ)
    {A : Set α} (hA : MeasurableSet A) {K : ℝ} (hK : ∀ x ∈ A, K ≤ |f x|)
    (hA0 : μ A ≠ 0) (N : ℕ) (Θ : ℝ≥0∞) (hΘ : (μ A)⁻¹ ^ (1 / r) ≤ Θ) :
    ENNReal.ofReal K ≤ ∑ k ∈ Finset.Icc 1 N, eLpNorm (vk k) ⊤ μ +
      Θ * ∑' k, (if N < k then eLpNorm (vk k) (ENNReal.ofReal r) μ else 0) := by
  have hAtop : μ A ≠ ⊤ := measure_ne_top μ A
  let g : ℕ → α → ℝ := fun M x => ∑ k ∈ Finset.Icc 1 M, vk k x
  have hgm : ∀ M, AEStronglyMeasurable (g M) μ := fun M =>
    Finset.aestronglyMeasurable_fun_sum _ (fun k hk => hvm k (Finset.mem_Icc.1 hk).1)
  let S1 : ℝ≥0∞ := ∑ k ∈ Finset.Icc 1 N, eLpNorm (vk k) ⊤ μ
  let S2 : ℝ≥0∞ := ∑' k, (if N < k then eLpNorm (vk k) (ENNReal.ofReal r) μ else 0)
  let P : ℝ≥0∞ := μ A * S1 + μ A ^ (1 - 1 / r) * S2
  let err : ℕ → ℝ≥0∞ := fun M => eLpNorm (fun x => f x - g M x) (ENNReal.ofReal r) μ *
    μ Set.univ ^ (1 - 1 / r)
  have hmain : ∀ M : ℕ, ENNReal.ofReal K * μ A ≤ P + err M := by
    intro M
    have h1 : ENNReal.ofReal K * μ A ≤ ∫⁻ x in A, ‖f x‖ₑ ∂μ := by
      calc ENNReal.ofReal K * μ A = ∫⁻ _ in A, ENNReal.ofReal K ∂μ := by simp
        _ ≤ ∫⁻ x in A, ‖f x‖ₑ ∂μ := by
          apply setLIntegral_mono' hA
          intro x hx
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hK x hx)
    have h2 : ∫⁻ x in A, ‖f x‖ₑ ∂μ ≤ ∫⁻ x in A, ‖g M x‖ₑ ∂μ +
        ∫⁻ x in A, ‖f x - g M x‖ₑ ∂μ := by
      rw [← lintegral_add_left' ((hgm M).enorm.restrict)]
      apply lintegral_mono
      intro x
      calc ‖f x‖ₑ = ‖g M x + (f x - g M x)‖ₑ := by rw [add_sub_cancel]
        _ ≤ _ := enorm_add_le _ _
    have h3 : ∫⁻ x in A, ‖g M x‖ₑ ∂μ ≤ ∑ k ∈ Finset.Icc 1 M, ∫⁻ x in A, ‖vk k x‖ₑ ∂μ := by
      rw [← lintegral_finsetSum']
      · exact lintegral_mono fun x => enorm_sum_le _ _
      · intro k hk
        exact ((hvm k (Finset.mem_Icc.1 hk).1).enorm).restrict
    have h4 : ∑ k ∈ Finset.Icc 1 M, ∫⁻ x in A, ‖vk k x‖ₑ ∂μ ≤ P := by
      calc ∑ k ∈ Finset.Icc 1 M, ∫⁻ x in A, ‖vk k x‖ₑ ∂μ
          ≤ ∑ k ∈ Finset.Icc 1 M, ((if k ≤ N then eLpNorm (vk k) ⊤ μ * μ A else 0) +
              (if N < k then eLpNorm (vk k) (ENNReal.ofReal r) μ * μ A ^ (1 - 1 / r) else 0)) := by
            apply Finset.sum_le_sum
            intro k hk
            have hk1 := (Finset.mem_Icc.1 hk).1
            by_cases hkN : k ≤ N
            · have : ¬ N < k := not_lt.2 hkN
              simp only [hkN, this, ite_true, ite_false, add_zero]
              exact lintegral_enorm_le_top (hvm k hk1) A
            · have : N < k := not_le.1 hkN
              simp only [hkN, this, ite_true, ite_false, zero_add]
              exact lintegral_enorm_le_lr (hvm k hk1) hr A
        _ = ∑ k ∈ Finset.Icc 1 M, (if k ≤ N then eLpNorm (vk k) ⊤ μ * μ A else 0) +
            ∑ k ∈ Finset.Icc 1 M, (if N < k then eLpNorm (vk k) (ENNReal.ofReal r) μ *
              μ A ^ (1 - 1 / r) else 0) := Finset.sum_add_distrib
        _ ≤ μ A * S1 + μ A ^ (1 - 1 / r) * S2 := by
            apply add_le_add
            · rw [Finset.mul_sum]
              calc _ = ∑ k ∈ (Finset.Icc 1 M).filter (· ≤ N), eLpNorm (vk k) ⊤ μ * μ A := by
                      rw [Finset.sum_filter]
                _ ≤ ∑ k ∈ Finset.Icc 1 N, eLpNorm (vk k) ⊤ μ * μ A := by
                      apply Finset.sum_le_sum_of_subset
                      intro k hk
                      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
                      exact ⟨hk.1.1, hk.2⟩
                _ = _ := by simp_rw [mul_comm (μ A)]
            · calc _ ≤ ∑ k ∈ Finset.Icc 1 M, μ A ^ (1 - 1 / r) *
                    (if N < k then eLpNorm (vk k) (ENNReal.ofReal r) μ else 0) := by
                    apply Finset.sum_le_sum
                    intro k _
                    split_ifs <;> simp [mul_comm]
                _ = μ A ^ (1 - 1 / r) * ∑ k ∈ Finset.Icc 1 M,
                    (if N < k then eLpNorm (vk k) (ENNReal.ofReal r) μ else 0) :=
                    (Finset.mul_sum _ _ _).symm
                _ ≤ _ := by
                    gcongr
                    exact ENNReal.sum_le_tsum _
    have h5 : ∫⁻ x in A, ‖f x - g M x‖ₑ ∂μ ≤ err M := by
      have hm : AEStronglyMeasurable (fun x => f x - g M x) μ := hfm.sub (hgm M)
      calc ∫⁻ x in A, ‖f x - g M x‖ₑ ∂μ ≤ ∫⁻ x, ‖f x - g M x‖ₑ ∂μ :=
            setLIntegral_le_lintegral _ _
        _ = eLpNorm (fun x => f x - g M x) 1 μ := (eLpNorm_one_eq_lintegral_enorm hm).symm
        _ ≤ err M := by
            have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
              simpa using ENNReal.ofReal_le_ofReal hr.le
            have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) hle hm
            rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_one, div_one] at h
            exact h
    calc ENNReal.ofReal K * μ A ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ P + err M := add_le_add (h3.trans h4) h5
  have herr : Tendsto err atTop (𝓝 0) := by
    have hexp : 0 ≤ 1 - 1 / r := by
      have : 1 / r ≤ 1 := by rw [div_le_one (by linarith)]; exact hr.le
      linarith
    have := ENNReal.Tendsto.mul_const hconv
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ Set.univ)))
    simpa only [zero_mul] using this
  have hlim : ENNReal.ofReal K * μ A ≤ P := by
    have ht : Tendsto (fun M => P + err M) atTop (𝓝 (P + 0)) := tendsto_const_nhds.add herr
    rw [add_zero] at ht
    exact ge_of_tendsto' ht hmain
  have hrw : μ A ^ (1 - 1 / r) = μ A * ((μ A)⁻¹) ^ (1 / r) := by
    rw [sub_eq_add_neg, ENNReal.rpow_add _ _ hA0 hAtop, ENNReal.rpow_one, ENNReal.rpow_neg,
      ENNReal.inv_rpow]
  have hP : P ≤ μ A * (S1 + Θ * S2) := by
    calc P = μ A * S1 + μ A ^ (1 - 1 / r) * S2 := rfl
      _ = μ A * S1 + μ A * ((μ A)⁻¹ ^ (1 / r) * S2) := by rw [hrw, mul_assoc]
      _ ≤ μ A * S1 + μ A * (Θ * S2) := by gcongr
      _ = _ := (mul_add _ _ _).symm
  have := hlim.trans hP
  rw [mul_comm (ENNReal.ofReal K)] at this
  exact (ENNReal.mul_le_mul_iff_right hA0 hAtop).1 this

end CoarseDeGiorgi.Endpoint.Potential
