import CoarseDeGiorgi.Foundations.FractionalSobolev.Kernel
import CoarseDeGiorgi.Foundations.FractionalSobolev.BandSums

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

/-- The explicit coefficient in the repaired DNPV Lemma 6.3. -/
def levelEstimateConstant (n : ℕ) (s p : ℝ) : ℝ :=
  2 * setEstimateConstant n (s * p) * (1 - 1 / (2 : ℝ) ^ p)

lemma levelEstimateConstant_pos {n : ℕ} (hn : 0 < n) (s : ℝ) {p : ℝ} (hp : 0 < p) :
    0 < levelEstimateConstant n s p := by
  have hT : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp
  unfold levelEstimateConstant
  exact mul_pos (mul_pos (by norm_num) (setEstimateConstant_pos hn _))
    (sub_pos.mpr (by simpa only [one_div] using inv_lt_one_of_one_lt₀ hT))

/-- Repaired DNPV Lemma 6.3: its selected pairs include the entire zero set. -/
theorem lemma_6_3 {n : ℕ} {s p : ℝ} (hs : 0 < s) (_hs1 : s < 1)
    (hp : 1 ≤ p) (hsp : s * p < (n : ℝ)) {f : Vec n → ℝ}
    (hf : Measurable f) (hcompact : HasCompactSupport f)
    (hbounded : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    ENNReal.ofReal (levelEstimateConstant n s p) *
      (∑' k : ℤ, volume (dyadicLevel f (k + 1)) *
        (volume (dyadicLevel f k)) ^ (-(s * p) / n) * sequenceWeight ((2 : ℝ) ^ p) k) ≤
      ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hnreal : (0 : ℝ) < n := (mul_pos hs hp0).trans hsp
  have hn : 0 < n := Nat.cast_pos.mp hnreal
  let θ := s * p / n
  let T := (2 : ℝ) ^ p
  let a := fun k : ℤ => volume (dyadicLevel f k)
  let d := fun k : ℤ => volume (dyadicBand f k)
  let S := ∑' i : ℤ, sequenceWeight T (i - 1) * (a (i - 1)) ^ (-θ) * d i
  let B := ∑' k : ℤ, a (k + 1) * (a k) ^ (-θ) * sequenceWeight T k
  have hT : 1 < T := Real.one_lt_rpow (by norm_num) hp0
  have hθ : 0 < θ := div_pos (mul_pos hs hp0) hnreal
  have ha : Antitone a := fun i j hij => measure_mono (dyadicLevel_antitone f hij)
  obtain ⟨M, hM⟩ := hbounded
  obtain ⟨N, hN⟩ := dyadicLevel_cutoff hM
  have hd : ∀ l, N ≤ l → d l = 0 := by
    intro l hl
    dsimp [d, dyadicBand]
    rw [hN l hl, Set.empty_sdiff, measure_empty]
  have hdecomp : ∀ i, a i = ∑ l ∈ Finset.Ico i N, d l :=
    dyadicLevel_measure_eq_sum hf (hN N le_rfl)
  have hBS : B ≤ ENNReal.ofReal (T / (T - 1)) * S := by
    have hh := band_sum_bound_shift hT hθ ha hd hdecomp
    have heq : (∑' i : ℤ, sequenceWeight T (i - 1) * (a (i - 1)) ^ (-θ) * a i) = B := by
      rw [← (Equiv.addRight (1 : ℤ)).tsum_eq]
      change (∑' k : ℤ, sequenceWeight T (k + 1 - 1) * (a (k + 1 - 1)) ^ (-θ) * a (k + 1)) = B
      simp only [add_sub_cancel_right]
      apply tsum_congr
      intro k
      ac_rfl
    rw [heq] at hh
    exact hh
  have hSE : 2 * ENNReal.ofReal (setEstimateConstant n (s * p)) * S ≤
      ∫⁻ xy : Vec n × Vec n, fracKernel s p f xy ∂(volume.prod volume) := by
    have hterm := ENNReal.tsum_le_tsum (selectedPairs_lower hn hs hp0 hf hcompact)
    have heq : (∑' i : ℤ, ENNReal.ofReal (setEstimateConstant n (s * p)) *
        sequenceWeight T (i - 1) * (a (i - 1)) ^ (-θ) * d i) =
        ENNReal.ofReal (setEstimateConstant n (s * p)) * S := by
      simp only [mul_assoc, S, ENNReal.tsum_mul_left]
    simp only [neg_div] at hterm
    change (∑' i : ℤ, ENNReal.ofReal (setEstimateConstant n (s * p)) *
        sequenceWeight T (i - 1) * (a (i - 1)) ^ (-θ) * d i) ≤ _ at hterm
    rw [heq] at hterm
    simpa only [mul_assoc] using (mul_le_mul' (le_rfl : (2 : ℝ≥0∞) ≤ 2) hterm).trans
      (selectedPairs_energy hf s p)
  have hconst : ENNReal.ofReal (levelEstimateConstant n s p) * ENNReal.ofReal (T / (T - 1)) =
      2 * ENNReal.ofReal (setEstimateConstant n (s * p)) := by
    rw [← ENNReal.ofReal_mul (levelEstimateConstant_pos hn s hp0).le]
    have heq : levelEstimateConstant n s p * (T / (T - 1)) =
        2 * setEstimateConstant n (s * p) := by
      unfold levelEstimateConstant
      change 2 * setEstimateConstant n (s * p) * (1 - 1 / T) * (T / (T - 1)) = _
      field_simp [ne_of_gt (lt_trans zero_lt_one hT), ne_of_gt (sub_pos.mpr hT)]
    rw [heq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  simp only [neg_div]
  change ENNReal.ofReal (levelEstimateConstant n s p) * B ≤ _
  calc
    _ ≤ ENNReal.ofReal (levelEstimateConstant n s p) * (ENNReal.ofReal (T / (T - 1)) * S) :=
      mul_le_mul' le_rfl hBS
    _ = 2 * ENNReal.ofReal (setEstimateConstant n (s * p)) * S := by rw [← mul_assoc, hconst]
    _ ≤ _ := hSE

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
