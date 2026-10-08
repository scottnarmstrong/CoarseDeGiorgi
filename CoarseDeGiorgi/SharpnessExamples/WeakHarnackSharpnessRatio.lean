import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessLimit

/-! # The ratio of the `L^η` mean to the infimum tends to infinity -/

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem whKc_nonneg {d : ℕ} (hd : 3 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε) (hε8 : ε < 1 / 8) :
    0 ≤ 4 * ε ^ 2 * ((8 * ε ^ 2) ^ (-((d : ℝ) / 2)) /
        (2 * ((Real.sqrt 8 * ε) ^ whBeta d q t * whLog d (2 * ε) ^ 3))) := by
  have hd1 : 1 ≤ d := by omega
  have hR1 : (1 : ℝ) ≤ whR d := by
    unfold whR; rw [Real.one_le_sqrt]; exact_mod_cast hd1
  have h2ε : 2 * ε ≤ whR d := by linarith
  have hℓ1 := one_le_whLog (d := d) (by positivity : 0 < 2 * ε) h2ε
  have : 0 < whLog d (2 * ε) ^ 3 := pow_pos (by linarith) 3
  positivity

theorem whRatio_tendsto {d : ℕ} [NeZero d] (hd : 3 ≤ d) {q t : ℝ} (hβ' : 0 < whBeta d q t) {η : ℝ}
    (hη : 0 < η)
    (hκ : (d : ℝ) < ((d : ℝ) + whBeta d q t - 2) * η) :
    Tendsto (fun ε : ℝ => normalizedLpMoment η hη (originCube (d := d) (5 / 8)) (whu d q t ε) /
      ENNReal.ofReal (whM d q t)) (𝓝[>] 0) (𝓝 ⊤) := by
  have hd1 : 1 ≤ d := by omega
  have hM := whM_pos hd q t
  set β := whBeta d q t with hβ
  set θ : ℝ := (((d : ℝ) + β - 2) * η - d) / (2 * η) with hθ
  have hθpos : 0 < θ := by
    apply div_pos _ (by positivity)
    linarith
  obtain ⟨C0, hC0, hG⟩ := whG_lower (d := d) hd (q := q) (t := t) hθpos
  have hp : (2 - (d : ℝ) - β + θ) * η + d < 0 := by
    have : θ * η = (((d : ℝ) + β - 2) * η - d) / 2 := by rw [hθ]; field_simp
    nlinarith
  obtain ⟨s, C, hs, hC, hZ⟩ := Z_lower_of_G hd1 hη hC0 hp (G := fun ε =>
    4 * ε ^ 2 * ((8 * ε ^ 2) ^ (-((d : ℝ) / 2)) /
          (2 * ((Real.sqrt 8 * ε) ^ whBeta d q t * whLog d (2 * ε) ^ 3)))) hG
  have hreal : Tendsto (fun ε : ℝ => C * ε ^ (-s) / whM d q t) (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun ε : ℝ => ε ^ (-s)) (𝓝[>] 0) atTop := by
      have := (tendsto_rpow_atTop hs).comp tendsto_inv_nhdsGT_zero
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [Function.comp_apply]
      rw [Real.inv_rpow (le_of_lt hε), Real.rpow_neg (le_of_lt hε)]
    exact (h1.const_mul_atTop hC).atTop_div_const hM
  have hofReal : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ (-s) / whM d q t)) (𝓝[>] 0)
      (𝓝 ⊤) := ENNReal.tendsto_ofReal_atTop.comp hreal
  refine tendsto_nhds_top_mono hofReal ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)] with ε hε
  have hG0 := whKc_nonneg hd q t hε.1 hε.2
  have hGle := whU_lower hd hβ' hε.1 hε.2
  have hmom := whMoment_lower hd q t hη hε.1 hε.2 hG0 hGle
  have hz := hZ ε hε.1 hε.2
  calc ENNReal.ofReal (C * ε ^ (-s) / whM d q t)
      = ENNReal.ofReal (C * ε ^ (-s)) / ENNReal.ofReal (whM d q t) := by
        rw [ENNReal.ofReal_div_of_pos hM]
    _ ≤ _ := by
        apply ENNReal.div_le_div_right
        exact (ENNReal.ofReal_le_ofReal hz).trans hmom

end

end CoarseDeGiorgi.SharpnessExamples
