import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Divergence of the ratio from a two-sided polynomial bound on `Θ_ε`

For every real `υ`, `Θ_ε^υ ≍ ε^{-aυ}` (end of the proof of Proposition
`p.sharpness.polynomial`); with a polynomial bound on the `L^η` norm this forces the ratio
to diverge exactly when `υ < b/a`. -/

open Filter Topology
open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

/-- `Θ^υ ≤ C^{|υ|} ε^{-aυ}` for every real `υ`, from two-sided bounds on `Θ`. -/
theorem optimalPowers_rpow_le {T : ℝ≥0∞} {z C : ℝ} (hz : 0 < z) (hC : 1 ≤ C) (υ : ℝ)
    (hup : T ≤ ENNReal.ofReal (C * z)) (hlo : ENNReal.ofReal (C⁻¹ * z) ≤ T) :
    T ^ υ ≤ ENNReal.ofReal (C ^ |υ| * z ^ υ) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  rcases le_or_gt 0 υ with hυ | hυ
  · calc T ^ υ ≤ (ENNReal.ofReal (C * z)) ^ υ := ENNReal.rpow_le_rpow hup hυ
      _ = ENNReal.ofReal ((C * z) ^ υ) := ENNReal.ofReal_rpow_of_pos (mul_pos hC0 hz)
      _ = ENNReal.ofReal (C ^ |υ| * z ^ υ) := by
        rw [Real.mul_rpow hC0.le hz.le, abs_of_nonneg hυ]
  · have h1 : (ENNReal.ofReal (C⁻¹ * z)) ^ (-υ) ≤ T ^ (-υ) :=
      ENNReal.rpow_le_rpow hlo (neg_nonneg.2 hυ.le)
    have h2 : T ^ υ ≤ (ENNReal.ofReal (C⁻¹ * z)) ^ υ := by
      have := ENNReal.inv_le_inv.2 h1
      rwa [← ENNReal.rpow_neg, ← ENNReal.rpow_neg, neg_neg] at this
    refine h2.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_pos (by positivity), abs_of_neg hυ,
      Real.mul_rpow (inv_nonneg.2 hC0.le) hz.le, Real.inv_rpow hC0.le, ← Real.rpow_neg hC0.le]

theorem optimalPowers_ratio_tendsto_top
    (T L : ℝ → ℝ≥0∞) {a b C B H υ : ℝ}
    (ha : 0 < a) (hC : 1 ≤ C) (hB : 1 ≤ B) (hH : 0 < H)
    (hυ : υ < b / a)
    (hTup : ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → T ε ≤ ENNReal.ofReal (C * ε ^ (-a)))
    (hTlo : ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → ENNReal.ofReal (C⁻¹ * ε ^ (-a)) ≤ T ε)
    (hL : ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → L ε ≤ ENNReal.ofReal (B * ε ^ b)) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal H / ((T ε) ^ υ * L ε)) (𝓝[>] 0) (𝓝 ⊤) := by
  have hgamma : a * υ - b < 0 := by
    have h := (lt_div_iff₀ ha).1 hυ
    nlinarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  set D := C ^ |υ| * B with hDdef
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos hC0 _) hB0
  have hlimit : Tendsto
      (fun ε : ℝ => ENNReal.ofReal ((H / D) * ε ^ (a * υ - b)))
      (𝓝[>] 0) (𝓝 ⊤) := by
    apply ENNReal.tendsto_ofReal_nhds_top.2
    exact (tendsto_rpow_neg_nhdsGT_zero hgamma).const_mul_atTop (div_pos hH hD)
  apply tendsto_nhds_top_mono hlimit
  have he8 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 / 8 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [self_mem_nhdsWithin, he8] with ε he he8
  have he0 : 0 < ε := he
  have hz : 0 < ε ^ (-a) := Real.rpow_pos_of_pos he0 _
  have hpower := optimalPowers_rpow_le hz hC υ (hTup ε he0 he8) (hTlo ε he0 he8)
  have hzυ : (ε ^ (-a)) ^ υ = ε ^ (-a * υ) := (Real.rpow_mul he0.le _ _).symm
  have hdenom : (T ε) ^ υ * L ε ≤ ENNReal.ofReal (D * ε ^ (b - a * υ)) := by
    calc _ ≤ ENNReal.ofReal (C ^ |υ| * (ε ^ (-a)) ^ υ) * ENNReal.ofReal (B * ε ^ b) :=
          mul_le_mul' hpower (hL ε he0 he8)
      _ = ENNReal.ofReal ((C ^ |υ| * (ε ^ (-a)) ^ υ) * (B * ε ^ b)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = _ := by
        congr 1
        rw [hzυ, hDdef]
        calc _ = (C ^ |υ| * B) * (ε ^ (-a * υ) * ε ^ b) := by ring
          _ = _ := by rw [← Real.rpow_add he0]; congr 2; ring
  have hquot : (H / D) * ε ^ (a * υ - b) = H / (D * ε ^ (b - a * υ)) := by
    rw [show a * υ - b = -(b - a * υ) by ring, Real.rpow_neg he0.le]
    field_simp
  calc _ = ENNReal.ofReal (H / (D * ε ^ (b - a * υ))) := by rw [hquot]
    _ = ENNReal.ofReal H / ENNReal.ofReal (D * ε ^ (b - a * υ)) :=
      ENNReal.ofReal_div_of_pos (mul_pos hD (Real.rpow_pos_of_pos he0 _))
    _ ≤ _ := ENNReal.div_le_div_left hdenom _

end CoarseDeGiorgi.SharpnessExamples
