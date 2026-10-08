import CoarseDeGiorgi.Foundations.FractionalSobolev.LevelEstimate
import CoarseDeGiorgi.Foundations.FractionalSobolev.LayerNorm
import CoarseDeGiorgi.Foundations.FractionalSobolev.Truncation

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The Sobolev constant `2^p · (2^p)^(1/α) / levelEstimateConstant n s p`, α = 1 - s p / n. -/
def sobolevConstant (n : ℕ) (s p : ℝ) : ℝ :=
  (2 : ℝ) ^ p * ((2 : ℝ) ^ p) ^ (1 / (1 - s * p / n)) / levelEstimateConstant n s p

lemma critical_parameters {n : ℕ} {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p)
    (hsp : s * p < (n : ℝ)) :
    0 < n ∧ 0 < 1 - s * p / n ∧ 1 - s * p / n ≤ 1 ∧
      1 ≤ dnpvCriticalExponent n s p ∧
      dnpvCriticalExponent n s p * (1 - s * p / n) = p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hn : (0 : ℝ) < n := (mul_pos hs hp0).trans hsp
  have hθ0 : 0 < s * p / n := div_pos (mul_pos hs hp0) hn
  have hθ1 : s * p / n < 1 := (div_lt_one hn).mpr hsp
  have hα : 0 < 1 - s * p / n := sub_pos.mpr hθ1
  have hα1 : 1 - s * p / n ≤ 1 := by linarith
  have hq0 : 0 < dnpvCriticalExponent n s p :=
    div_pos (mul_pos hn hp0) (sub_pos.mpr hsp)
  have hqp : dnpvCriticalExponent n s p * (1 - s * p / n) = p := by
    unfold dnpvCriticalExponent
    field_simp [hn.ne', (sub_pos.mpr hsp).ne',
      (show (n : ℝ) - p * s ≠ 0 by nlinarith)]
  refine ⟨Nat.cast_pos.mp hn, hα, hα1, ?_, hqp⟩
  nlinarith

lemma sobolevConstant_pos {n : ℕ} {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p)
    (hsp : s * p < (n : ℝ)) : 0 < sobolevConstant n s p := by
  have hn := (critical_parameters hs hp hsp).1
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _))
    (levelEstimateConstant_pos hn s hp0)

/-- The bounded-function step of DNPV Theorem 6.5. -/
theorem sobolev_bounded {n : ℕ} {s p : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp : 1 ≤ p) (hsp : s * p < (n : ℝ)) {f : Vec n → ℝ}
    (hf : Measurable f) (hcompact : HasCompactSupport f)
    (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    (eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) volume).rpow p ≤
      ENNReal.ofReal (sobolevConstant n s p) *
        ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume) := by
  obtain ⟨hn, hα, hα1, hq, hqp⟩ := critical_parameters hs hp hsp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let θ := s * p / n
  let T := (2 : ℝ) ^ p
  let a := fun k : ℤ => volume (dyadicLevel f k)
  let B := ∑' k : ℤ, a (k + 1) * (a k) ^ (-θ) * sequenceWeight T k
  let E := ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume)
  have hθ : 0 < θ := div_pos (mul_pos hs hp0) (Nat.cast_pos.mpr hn)
  have hθ1 : θ < 1 := by dsimp [θ] at *; linarith
  have hT : 1 < T := Real.one_lt_rpow (by norm_num) hp0
  have ha : Antitone a := fun _ _ hij => measure_mono (dyadicLevel_antitone f hij)
  obtain ⟨M, hM, hab⟩ := dyadicLevel_measure_bound hcompact
  obtain ⟨R, hR⟩ := hbounded
  obtain ⟨N, hN⟩ := dyadicLevel_cutoff hR
  have hazero : ∀ k, N ≤ k → a k = 0 := by
    intro k hk
    dsimp [a]
    rw [hN k hk, measure_empty]
  have hsequence := lemma_6_2 hT hθ hθ1 ha hM hab hazero
  have hlevel := lemma_6_3 hs hs1 hp hsp hf hcompact ⟨R, hR⟩
  simp only [neg_div] at hlevel
  change ENNReal.ofReal (levelEstimateConstant n s p) * B ≤ E at hlevel
  have hC : 0 < levelEstimateConstant n s p := levelEstimateConstant_pos hn s hp0
  have hC0 : ENNReal.ofReal (levelEstimateConstant n s p) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  have hB : B ≤ E / ENNReal.ofReal (levelEstimateConstant n s p) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl ENNReal.ofReal_ne_top)).mpr (by simpa only [mul_comm] using hlevel)
  calc
    _ ≤ ENNReal.ofReal T * ∑' k : ℤ, (a k) ^ (1 - θ) * sequenceWeight T k :=
      layer_norm_le hp0 (lt_of_lt_of_le zero_lt_one hq) hα hα1 hqp hf
    _ ≤ ENNReal.ofReal T * ((ENNReal.ofReal T) ^ (1 / (1 - θ)) * B) :=
      mul_le_mul' le_rfl hsequence
    _ ≤ ENNReal.ofReal T * ((ENNReal.ofReal T) ^ (1 / (1 - θ)) *
        (E / ENNReal.ofReal (levelEstimateConstant n s p))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hB)
    _ = ENNReal.ofReal (sobolevConstant n s p) * E := by
      rw [ENNReal.ofReal_rpow_of_pos (lt_trans zero_lt_one hT)]
      unfold sobolevConstant
      change _ = ENNReal.ofReal (T * T ^ (1 / (1 - θ)) / levelEstimateConstant n s p) * E
      rw [ENNReal.ofReal_div_of_pos hC, ENNReal.ofReal_mul (lt_trans zero_lt_one hT).le]
      simp only [div_eq_mul_inv]
      ac_rfl

/-- DNPV Theorem 6.5, with exactly the statement `dnpv_theorem_6_5`, proved without importing it. -/
theorem dnpv_theorem_6_5_proved :
    ∀ n : ℕ, ∀ s p : ℝ, 0 < s → s < 1 → 1 ≤ p → s * p < (n : ℝ) →
    ∃ C : ℝ, 0 < C ∧
    ∀ f : Vec n → ℝ, Measurable f → HasCompactSupport f →
    (eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) volume).rpow p ≤
      ENNReal.ofReal C *
      ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume) := by
  intro n s p hs hs1 hp hsp
  refine ⟨sobolevConstant n s p, sobolevConstant_pos hs hp hsp, ?_⟩
  intro f hf hcompact
  have hq := (critical_parameters hs hp hsp).2.2.2.1
  have hlimit := (ENNReal.continuous_rpow_const (y := p)).tendsto
    (eLpNorm f (ENNReal.ofReal (dnpvCriticalExponent n s p)) volume)
  apply le_of_tendsto' (hlimit.comp (lemma_6_4 hq hf))
  intro N
  have hb : ∃ M : ℝ, ∀ x, |truncate f N x| ≤ M := by
    refine ⟨N, fun x => ?_⟩
    rw [abs_truncate]
    exact min_le_right _ _
  exact (sobolev_bounded hs hs1 hp hsp (truncate_measurable hf N)
    (truncate_compact_support hcompact N) hb).trans
      (mul_le_mul' le_rfl (truncate_energy_le (lt_of_lt_of_le zero_lt_one hp).le f N))

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
