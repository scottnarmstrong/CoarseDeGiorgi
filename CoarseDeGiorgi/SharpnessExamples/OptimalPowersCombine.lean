import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Combining the upper bounds with a lower bound on the contrast

`Θ = Λ / λ`, `Λ ≤ C z`, `C⁻¹ ≤ λ` and `c z ≤ Θ` give two-sided bounds for `Λ`, `λ` and `Θ`
(Proposition `p.sharpness.polynomial`, end of Step 3). -/

open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

/-- The common constant of `optimalPowers_combine`. -/
noncomputable def optimalPowersConst (C1 c : ℝ) : ℝ :=
  max 1 (max C1 (max (C1 / c) (max c⁻¹ (C1 ^ 2))))

theorem optimalPowersConst_one_le (C1 c : ℝ) : 1 ≤ optimalPowersConst C1 c := le_max_left _ _

theorem optimalPowers_combine {L l T : ℝ≥0∞} {z C1 c : ℝ} (hz : 0 < z) (hC1 : 1 ≤ C1)
    (hc : 0 < c) (hT : T = L / l) (hup : L ≤ ENNReal.ofReal (C1 * z))
    (hlo : ENNReal.ofReal C1⁻¹ ≤ l) (hTlo : ENNReal.ofReal (c * z) ≤ T) :
    let C := optimalPowersConst C1 c
    ENNReal.ofReal (C⁻¹ * z) ≤ L ∧ L ≤ ENNReal.ofReal (C * z) ∧
      ENNReal.ofReal C⁻¹ ≤ l ∧ l ≤ ENNReal.ofReal C ∧
      ENNReal.ofReal (C⁻¹ * z) ≤ T ∧ T ≤ ENNReal.ofReal (C * z) := by
  have hC10 : 0 < C1 := lt_of_lt_of_le zero_lt_one hC1
  have hcz : 0 < c * z := mul_pos hc hz
  have hl0 : l ≠ 0 := by
    intro h; rw [h] at hlo
    exact absurd (ENNReal.ofReal_pos.2 (inv_pos.2 hC10)) (by simpa using hlo)
  have hltop : l ≠ ⊤ := by
    intro h
    rw [h, ENNReal.div_top] at hT
    rw [hT] at hTlo
    exact absurd (ENNReal.ofReal_pos.2 hcz) (by simpa using hTlo)
  have hLeq : L = T * l := by
    rw [hT, ENNReal.div_mul_cancel hl0 hltop]
  have hT0 : T ≠ 0 := by
    intro h; rw [h] at hTlo
    exact absurd (ENNReal.ofReal_pos.2 hcz) (by simpa using hTlo)
  intro C
  have hC : C = max 1 (max C1 (max (C1 / c) (max c⁻¹ (C1 ^ 2)))) := rfl
  have hCa : C1 ≤ C := hC ▸ le_max_of_le_right (le_max_left _ _)
  have hCb : C1 / c ≤ C := hC ▸ le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCc : c⁻¹ ≤ C := hC ▸
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hCd : C1 ^ 2 ≤ C := hC ▸
    le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
  have hC0 : 0 < C := lt_of_lt_of_le hC10 hCa
  have hCinv : C⁻¹ ≤ c * C1⁻¹ := by
    have := inv_anti₀ (div_pos hC10 hc) hCb
    rwa [inv_div, div_eq_mul_inv] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLeq]
    calc ENNReal.ofReal (C⁻¹ * z) ≤ ENNReal.ofReal ((c * z) * C1⁻¹) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = ENNReal.ofReal (c * z) * ENNReal.ofReal C1⁻¹ :=
          ENNReal.ofReal_mul hcz.le
      _ ≤ T * l := mul_le_mul' hTlo hlo
  · exact hup.trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  · exact hlo.trans' (ENNReal.ofReal_le_ofReal (inv_anti₀ hC10 hCa))
  · have h1 : ENNReal.ofReal (c * z) * l ≤ ENNReal.ofReal (C1 * z) :=
      calc _ ≤ T * l := mul_le_mul' hTlo le_rfl
        _ = L := hLeq.symm
        _ ≤ _ := hup
    have h2 : l ≤ ENNReal.ofReal (C1 * z) / ENNReal.ofReal (c * z) :=
      (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hcz)) (Or.inl ENNReal.ofReal_ne_top)).2
        (by rwa [mul_comm] at h1)
    rw [← ENNReal.ofReal_div_of_pos hcz] at h2
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show C1 * z / (c * z) = C1 / c by field_simp]
    exact hCb
  · refine hTlo.trans' (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [inv_le_comm₀ hc hC0 |>.1 (by simpa using hCc)]
  · have h1 : T ≤ ENNReal.ofReal (C1 * z) / ENNReal.ofReal C1⁻¹ := by
      rw [hT]; exact ENNReal.div_le_div hup hlo
    rw [← ENNReal.ofReal_div_of_pos (inv_pos.2 hC10)] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show C1 * z / C1⁻¹ = C1 ^ 2 * z by field_simp]
    nlinarith

end CoarseDeGiorgi.SharpnessExamples
