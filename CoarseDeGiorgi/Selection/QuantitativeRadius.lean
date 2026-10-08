import CoarseDeGiorgi.Selection.CommonRadius
import CoarseDeGiorgi.Selection.Maximal

namespace CoarseDeGiorgi.Selection

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Normalized weak estimate, including the zero-energy case. -/
theorem normalized_maximal_bad_set_bound (ν : Measure ℝ) [Measure.InnerRegular ν]
    {K E : ℝ≥0∞} (hK0 : K ≠ 0) (hKtop : K ≠ ⊤) (hEtop : E ≠ ⊤)
    (hmass : ν univ ≤ 2 * E) :
    volume {τ | 6 * K * E < centeredMaximal ν τ} ≤ K⁻¹ := by
  by_cases hE0 : E = 0
  · subst E
    have hν : ν = 0 := Measure.measure_univ_eq_zero.mp (by simpa using hmass)
    subst ν
    have he : {τ | 6 * K * 0 < centeredMaximal 0 τ} = ∅ := by
      ext τ; simp [centeredMaximal]
    rw [he, measure_empty]
    exact zero_le
  have hT0 : 6 * K * E ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hK0) hE0
  have hTtop : 6 * K * E ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hKtop))
      (lt_top_iff_ne_top.mpr hEtop)).ne
  have hΓ : 0 < (6 * K * E).toReal := ENNReal.toReal_pos hT0 hTtop
  have hb := centeredMaximal_weak_bound ν hΓ
  rw [ENNReal.ofReal_toReal hTtop] at hb
  apply hb.trans
  calc
    3 * ν univ / (6 * K * E) ≤ 3 * (2 * E) / (6 * K * E) := by gcongr
    _ = (6 * E) / ((6 * K) * E) := by rw [← mul_assoc]; norm_num
    _ = 6 / (6 * K) := ENNReal.mul_div_mul_right _ _ hE0 hEtop
    _ = K⁻¹ := by
      simpa only [mul_one, one_div] using ENNReal.mul_div_mul_left (1 : ℝ≥0∞) K
        (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num : (6 : ℝ≥0∞) ≠ ⊤)

/-- One radius for any finite family of strong bounds and the centered energy weak bound.
In the manuscript, the strong family is response, fractional trace, and the optional L² trace; any
additional a.e. trace/subsequence property is retained through `Good`. -/
theorem one_radius_of_integral_bounds {ι : Type*} [Fintype ι] {J : Set ℝ}
    (ν : Measure ℝ) [Measure.InnerRegular ν] {E K : ℝ≥0∞}
    (hK0 : K ≠ 0) (hKtop : K ≠ ⊤) (hEtop : E ≠ ⊤) (hmass : ν univ ≤ 2 * E)
    (f : ι → ℝ → ℝ≥0∞) (exponent : ι → ℝ) (B : ι → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hr : ∀ i, 0 < exponent i)
    (hint : ∀ i, ∫⁻ τ in J, (f i τ) ^ exponent i ≤ (B i) ^ exponent i)
    {Good : ℝ → Prop} (hgood : ∀ᵐ τ ∂volume.restrict J, Good τ)
    (hsmall : ((Fintype.card ι + 1 : ℕ) : ℝ≥0∞) * K⁻¹ < volume J) :
    ∃ τ ∈ J, Good τ ∧ (∀ i, f i τ ≤ K ^ (1 / exponent i) * B i) ∧
      centeredMaximal ν τ ≤ 6 * K * E := by
  classical
  let g : Option ι → ℝ → ℝ≥0∞ := fun o => o.elim (centeredMaximal ν) f
  let T : Option ι → ℝ≥0∞ := fun o => o.elim (6 * K * E) (fun i => K ^ (1 / exponent i) * B i)
  have hb (o : Option ι) : (volume.restrict J) {τ | T o < g o τ} ≤ K⁻¹ := by
    cases o with
    | none =>
      exact (Measure.restrict_le_self (μ := (volume : Measure ℝ)) (s := J) _).trans
        (normalized_maximal_bad_set_bound ν hK0 hKtop hEtop hmass)
    | some i => exact normalized_bad_set_bound (hf i) (hr i) hK0 hKtop (hint i)
  have hs : ∑ _o : Option ι, K⁻¹ < volume J := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_option, nsmul_eq_mul] using hsmall
  obtain ⟨τ, hτ, hg, hall⟩ := exists_common_radius_of_local_bad_set_bounds hgood hb hs
  exact ⟨τ, hτ, hg, fun i => hall (some i), hall none⟩


end

end CoarseDeGiorgi.Selection
