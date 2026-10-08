import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicFields

/-! # Circular sup-distance and compact-support envelopes -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization Set

noncomputable section

variable {d : ℕ}

/-- A short coordinate displacement can decrease circular distance by at most its length. -/
theorem abs_le_abs_wrapCoordinate_add {m : ℤ} {t s : ℝ}
    (ht : t ∈ Ico (-auxSide m) (auxSide m)) (hs : |s| ≤ auxSide m) :
    |t| ≤ |wrapCoordinate m (t + s)| + |s| := by
  have hL := auxSide_pos m
  obtain ⟨hslo, hshi⟩ := abs_le.mp hs
  by_cases hlo : t + s < -auxSide m
  · have hsneg : s < 0 := by linarith [ht.1]
    have htneg : t < 0 := by linarith
    have hw : wrapCoordinate m (t + s + 2 * auxSide m) = t + s + 2 * auxSide m := by
      apply (toIcoMod_eq_self _).mpr
      constructor <;> linarith [ht.1]
    rw [wrapCoordinate_add_period] at hw
    rw [hw, abs_of_nonpos htneg.le, abs_of_nonpos hsneg.le,
      abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.1]
  · by_cases hhi : auxSide m ≤ t + s
    · have hspos : 0 ≤ s := by linarith [ht.2]
      have htpos : 0 ≤ t := by linarith
      have hw : wrapCoordinate m (t + s - 2 * auxSide m) = t + s - 2 * auxSide m := by
        apply (toIcoMod_eq_self _).mpr
        constructor <;> linarith [ht.2]
      have hp : wrapCoordinate m (t + s - 2 * auxSide m + 2 * auxSide m) =
          wrapCoordinate m (t + s - 2 * auxSide m) := wrapCoordinate_add_period m _
      rw [sub_add_cancel, hw] at hp
      rw [hp, abs_of_nonneg htpos, abs_of_nonneg hspos,
        abs_of_nonpos (by linarith [ht.2])]
      linarith [ht.2]
    · have hw : wrapCoordinate m (t + s) = t + s := by
        apply (toIcoMod_eq_self _).mpr
        constructor <;> linarith
      rw [hw]
      have h := abs_add_le (t + s) (-s)
      simpa only [add_neg_cancel_right, abs_neg] using h

/-- Wrapped sup-distance satisfies the short-displacement triangle inequality. -/
theorem norm_wrapBox_le_add {m : ℤ} (v s : Vec d) (hs : ‖s‖ ≤ auxSide m) :
    ‖wrapBox m v‖ ≤ ‖wrapBox m (v + s)‖ + ‖s‖ := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  have hi0 : |s i| ≤ ‖s‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm s i
  have hi : |s i| ≤ auxSide m := hi0.trans hs
  have h := abs_le_abs_wrapCoordinate_add (wrapCoordinate_mem_Ico m (v i)) hi
  have hw : wrapCoordinate m (wrapCoordinate m (v i) + s i) =
      wrapCoordinate m (v i + s i) := by
    rw [add_comm (wrapCoordinate m (v i)) (s i), add_comm (v i) (s i)]
    have heq : s i + wrapCoordinate m (v i) = s i + v i - (v i - wrapCoordinate m (v i)) := by ring
    rw [heq, wrapCoordinate_sub_periodShift]
  rw [hw] at h
  exact h.trans (add_le_add
    (by simpa only [wrapBox, Pi.add_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (wrapBox m (v + s)) i)
    (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm s i))

/-- Translating a wrapped compact support never moves it farther than the displacement. -/
theorem norm_wrapBox_gt_of_norm_gt {m : ℤ} {R : ℝ} (v s : Vec d)
    (hs : ‖s‖ ≤ auxSide m) (hv : R + ‖s‖ < ‖wrapBox m v‖) :
    R < ‖wrapBox m (v + s)‖ := by
  have h := norm_wrapBox_le_add v s hs
  linarith

end

end CoarseDeGiorgi.Foundations.Reconstruction
