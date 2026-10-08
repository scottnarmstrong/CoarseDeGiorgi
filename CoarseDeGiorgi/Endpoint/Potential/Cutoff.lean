module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Potential

open Real intervalIntegral

/-- A smooth cutoff derivative: `1` on `[-K, K]`, vanishing outside `[-2K, 2K]`. -/
noncomputable def psiCut (K : ℝ) (s : ℝ) : ℝ := smoothTransition (2 - s ^ 2 / K ^ 2)

/-- A smooth bounded function equal to the identity on `[-K, K]`. -/
noncomputable def phiCut (K : ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, psiCut K s

theorem psiCut_contDiff (K : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psiCut K) :=
  smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_id.pow 2).div_const _))

theorem psiCut_nonneg (K s : ℝ) : 0 ≤ psiCut K s := smoothTransition.nonneg _

theorem psiCut_le_one (K s : ℝ) : psiCut K s ≤ 1 := smoothTransition.le_one _

theorem psiCut_eq_one {K : ℝ} (hK : 0 < K) {s : ℝ} (hs : |s| ≤ K) : psiCut K s = 1 := by
  unfold psiCut
  apply smoothTransition.one_of_one_le
  have h : s ^ 2 ≤ K ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg s) hs 2
  have : s ^ 2 / K ^ 2 ≤ 1 := (div_le_one (by positivity)).2 h
  linarith

theorem psiCut_eq_zero {K : ℝ} (hK : 0 < K) {s : ℝ} (hs : 2 * K ≤ |s|) : psiCut K s = 0 := by
  unfold psiCut
  apply smoothTransition.zero_of_nonpos
  have h : (2 * K) ^ 2 ≤ s ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (by positivity) hs 2
  have : 4 ≤ s ^ 2 / K ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

theorem phiCut_hasDerivAt (K t : ℝ) : HasDerivAt (phiCut K) (psiCut K t) t :=
  ((psiCut_contDiff K).continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem phiCut_contDiff (K : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phiCut K) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (phiCut_hasDerivAt K t).differentiableAt,
    by
      have : deriv (phiCut K) = psiCut K := funext fun t => (phiCut_hasDerivAt K t).deriv
      rw [this]; exact psiCut_contDiff K⟩

theorem deriv_phiCut (K : ℝ) : deriv (phiCut K) = psiCut K :=
  funext fun t => (phiCut_hasDerivAt K t).deriv

theorem phiCut_zero (K : ℝ) : phiCut K 0 = 0 := by simp [phiCut]

theorem abs_deriv_phiCut_le (K t : ℝ) : |deriv (phiCut K) t| ≤ 1 := by
  rw [deriv_phiCut, abs_of_nonneg (psiCut_nonneg K t)]; exact psiCut_le_one K t

theorem phiCut_abs_le_of_abs_le {K : ℝ} {t : ℝ} (ht : |t| ≤ 2 * K) : |phiCut K t| ≤ 2 * K := by
  unfold phiCut
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := psiCut K) (C := 1) (fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (psiCut_nonneg K x)]; exact psiCut_le_one K x)
  rw [Real.norm_eq_abs, sub_zero, one_mul] at h
  exact h.trans ht

theorem phiCut_abs_le {K : ℝ} (hK : 0 < K) (t : ℝ) : |phiCut K t| ≤ 2 * K := by
  rcases le_or_gt (|t|) (2 * K) with h | h
  · exact phiCut_abs_le_of_abs_le h
  · have hz : ∀ s : ℝ, 2 * K ≤ |s| → psiCut K s = 0 := fun s hs => psiCut_eq_zero hK hs
    rcases le_or_gt 0 t with ht | ht
    · have ht' : 2 * K < t := by rwa [abs_of_nonneg ht] at h
      have hs : phiCut K t = phiCut K (2 * K) := by
        unfold phiCut
        rw [← integral_add_adjacent_intervals
          ((psiCut_contDiff K).continuous.intervalIntegrable 0 (2 * K))
          ((psiCut_contDiff K).continuous.intervalIntegrable (2 * K) t)]
        have : ∫ s in (2 * K)..t, psiCut K s = 0 := by
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
          · simp
          · intro s hs
            rw [Set.uIcc_of_le ht'.le] at hs
            apply hz
            rw [abs_of_nonneg (by linarith [hs.1])]; exact hs.1
        rw [this, add_zero]
      rw [hs]
      exact phiCut_abs_le_of_abs_le (by rw [abs_of_pos (by linarith)])
    · have ht' : t < -(2 * K) := by
        rw [abs_of_neg ht] at h; linarith
      have hs : phiCut K t = phiCut K (-(2 * K)) := by
        unfold phiCut
        rw [← integral_add_adjacent_intervals
          ((psiCut_contDiff K).continuous.intervalIntegrable 0 (-(2 * K)))
          ((psiCut_contDiff K).continuous.intervalIntegrable (-(2 * K)) t)]
        have : ∫ s in (-(2 * K))..t, psiCut K s = 0 := by
          rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
          · simp
          · intro s hs
            rw [Set.uIcc_of_ge ht'.le] at hs
            apply hz
            rw [abs_of_nonpos (by linarith [hs.2])]; linarith [hs.2]
        rw [this, add_zero]
      rw [hs]
      exact phiCut_abs_le_of_abs_le (by rw [abs_neg, abs_of_pos (by linarith)])

end CoarseDeGiorgi.Endpoint.Potential
