import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessCoefficient

/-! # The weak Harnack radial field is a weighted coefficient -/

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The radial profile as a nonnegative function on all of `ℝ`. -/
def whField (d : ℕ) (q t : ℝ) (ρ : ℝ) : ℝ := |whA d q t ρ|

/-- The coefficient field `a(|x|) I`. -/
def whCoeff (d : ℕ) (q t : ℝ) : CoeffField d :=
  fun x => whField d q t (euclidNorm x) • (1 : Mat d)

theorem whField_nonneg (d : ℕ) (q t ρ : ℝ) : 0 ≤ whField d q t ρ := abs_nonneg _

theorem whField_eq {d : ℕ} {q t : ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hR : ρ ≤ whR d) :
    whField d q t ρ = whA d q t ρ :=
  abs_of_pos (whA_pos hρ hR)

theorem whField_zero {d : ℕ} {q t : ℝ} (hβ : 0 < whBeta d q t) : whField d q t 0 = 0 := by
  unfold whField
  rw [whA_zero hβ, abs_zero]

theorem measurable_whA (d : ℕ) (q t : ℝ) : Measurable (whA d q t) := by
  unfold whA whLog
  fun_prop

theorem measurable_whField (d : ℕ) (q t : ℝ) : Measurable (whField d q t) :=
  by
  show Measurable (fun ρ => |whA d q t ρ|)
  simpa [Real.norm_eq_abs] using (measurable_whA d q t).norm

theorem measurable_whWeight (d : ℕ) (q t : ℝ) :
    Measurable (fun x : Vec d => whField d q t (euclidNorm x)) :=
  (measurable_whField d q t).comp continuous_euclidNorm.measurable

theorem whField_le {d : ℕ} (hd : 1 ≤ d) {q t : ℝ} (hβ : 0 < whBeta d q t) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (hR : ρ ≤ whR d) :
    whField d q t ρ ≤ (Real.exp 1 * whR d) ^ whBeta d q t / (whBeta d q t / 3) ^ 3 := by
  rcases h0.eq_or_lt with h | h
  · subst h
    rw [whField_zero hβ]
    positivity
  · rw [whField_eq h hR]
    exact whA_le hd hβ h hR

theorem whNear_nonneg (β h : ℝ) {r : ℝ} (hr : 0 ≤ r) (h1 : h ≤ 1) : 0 ≤ whNear β h r := by
  unfold whNear
  by_cases hrh : r < h
  · simp only [hrh, ↓reduceIte]
    exact whOmega_nonneg β hr (hrh.le.trans h1)
  · simp only [hrh, ↓reduceIte]; exact le_rfl

theorem whFar_nonneg (β h : ℝ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ whFar β h r := by
  unfold whFar
  by_cases hc : h ≤ r ∧ r < 1
  · simp only [hc, and_self, ↓reduceIte]
    exact whOmega_nonneg β hr hc.2.le
  · simp only [hc, ↓reduceIte]; exact le_rfl

theorem whFar_le {β h : ℝ} (hβ : 0 ≤ β) (h0 : 0 < h) {r : ℝ} : whFar β h r ≤ h ^ (-β) := by
  unfold whFar
  by_cases hc : h ≤ r ∧ r < 1
  · simp only [hc, and_self, ↓reduceIte]
    have hr0 : 0 < r := h0.trans_le hc.1
    unfold whOmega
    have h1 : 0 ≤ 1 - Real.log r := by linarith [Real.log_nonpos hr0.le hc.2.le]
    have h2 : (1 - Real.log r) ^ (-3 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.log_nonpos hr0.le hc.2.le])
        (by norm_num)
    have h3 : r ^ (-β) ≤ h ^ (-β) := Real.rpow_le_rpow_of_nonpos h0 hc.1 (by linarith)
    calc r ^ (-β) * (1 - Real.log r) ^ (-3 : ℝ) ≤ r ^ (-β) * 1 :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hr0.le _)
      _ ≤ h ^ (-β) := by rw [mul_one]; exact h3
  · simp only [hc, ↓reduceIte]
    exact (Real.rpow_pos_of_pos h0 _).le

/-- The reciprocal of the field is dominated by the radial majorant. -/
theorem whField_inv_le {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t) {x : Vec d}
    (hx : x ∈ originCube (d := d) 1) {h : ℝ} (h1 : h ≤ 1) :
    (whField d q t (euclidNorm x))⁻¹ ≤ whNear (whBeta d q t) h ‖x‖ + whFar (whBeta d q t) h ‖x‖ := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hxn : ‖x‖ < 1 / 2 := (mem_originCube_iff x).1 hx
  have hRpos := whR_pos hd
  have hR1 : (1 : ℝ) ≤ whR d := by
    unfold whR
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  have hsum : 0 ≤ whNear (whBeta d q t) h ‖x‖ + whFar (whBeta d q t) h ‖x‖ :=
    add_nonneg (whNear_nonneg _ _ (norm_nonneg x) h1) (whFar_nonneg _ _ (norm_nonneg x))
  by_cases hx0 : x = 0
  · subst hx0
    rw [(euclidNorm_eq_zero_iff (0 : Vec d)).2 rfl, whField_zero hβ]
    simpa using hsum
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  set β := whBeta d q t with hβdef
  set ρ := euclidNorm x with hρ
  have hρ1 : ‖x‖ ≤ ρ := norm_le_euclidNorm x
  have hρ2 : ρ ≤ whR d * ‖x‖ := euclidNorm_le x
  have hρpos : 0 < ρ := hxpos.trans_le hρ1
  have hρR : ρ ≤ whR d := by nlinarith
  rw [whField_eq hρpos hρR]
  -- the bound by ω
  have hω : (whA d q t ρ)⁻¹ ≤ whOmega β ‖x‖ := by
    unfold whA whOmega
    have hl : 1 - Real.log ‖x‖ ≤ whLog d ρ := by
      unfold whLog
      have : Real.log ρ ≤ Real.log (whR d * ‖x‖) := Real.log_le_log hρpos hρ2
      rw [Real.log_mul hRpos.ne' hxpos.ne'] at this
      linarith
    have hl1 : 0 < 1 - Real.log ‖x‖ := by
      have : Real.log ‖x‖ ≤ 0 := Real.log_nonpos hxpos.le (by linarith)
      linarith
    have e1 : (ρ ^ β * whLog d ρ ^ 3)⁻¹ = ρ ^ (-β) * (whLog d ρ) ^ (-3 : ℝ) := by
      rw [mul_inv, Real.rpow_neg hρpos.le, ← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
      norm_num
    rw [e1]
    have h2 : ρ ^ (-β) ≤ ‖x‖ ^ (-β) := Real.rpow_le_rpow_of_nonpos hxpos hρ1 (by linarith)
    have h3 : whLog d ρ ^ (-3 : ℝ) ≤ (1 - Real.log ‖x‖) ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hl1 hl (by norm_num)
    exact mul_le_mul h2 h3 (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hxpos.le _)
  refine hω.trans ?_
  unfold whNear whFar
  by_cases hxh : ‖x‖ < h
  · have : ¬ (h ≤ ‖x‖ ∧ ‖x‖ < 1) := fun hh => absurd hh.1 (not_le.2 hxh)
    simp [hxh, this]
  · have h2 : h ≤ ‖x‖ ∧ ‖x‖ < 1 := ⟨not_lt.1 hxh, by linarith⟩
    simp [hxh, h2]

theorem whFar_one (β r : ℝ) : whFar β 1 r = 0 := by
  unfold whFar
  have : ¬ (1 ≤ r ∧ r < 1) := fun h => absurd h.1 (not_le.2 h.2)
  simp [this]

theorem norm_lt_R_of_mem {d : ℕ} [NeZero d] {x : Vec d} (hx : x ∈ originCube (d := d) 1) :
    euclidNorm x ≤ whR d := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hxn : ‖x‖ < 1 / 2 := (mem_originCube_iff x).1 hx
  have hR1 : (1 : ℝ) ≤ whR d := by
    unfold whR
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  have := euclidNorm_le x
  nlinarith [norm_nonneg x]

theorem whInv_integrable {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t)
    (hβd : whBeta d q t < d) :
    IntegrableOn (fun x : Vec d => (whField d q t (euclidNorm x))⁻¹) (originCube 1) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hnear := (integrable_polar_pi (d := d)
    (f := whNear (whBeta d q t) 1)).2 (near_integral hd hβd one_pos le_rfl).1
  refine hnear.integrableOn.mono' (measurable_whWeight d q t).inv.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_originCube] with x hx
  have h := whField_inv_le hβ hx (le_refl (1 : ℝ))
  rw [whFar_one, add_zero] at h
  rw [Real.norm_of_nonneg (inv_nonneg.2 (whField_nonneg _ _ _ _))]
  exact h

theorem whWeight_integrable {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t) :
    IntegrableOn (fun x : Vec d => whField d q t (euclidNorm x)) (originCube 1) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  refine Measure.integrableOn_of_bounded (M := (Real.exp 1 * whR d) ^ whBeta d q t /
    (whBeta d q t / 3) ^ 3) volume_originCube_ne_top
    (measurable_whWeight d q t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_originCube] with x hx
  rw [Real.norm_of_nonneg (whField_nonneg _ _ _ _)]
  exact whField_le hd hβ (euclidNorm_nonneg' x) (norm_lt_R_of_mem hx)

theorem whCoeff_weightedCoeffOn {d : ℕ} [NeZero d] {q t : ℝ} (hβ : 0 < whBeta d q t)
    (hβd : whBeta d q t < d) :
    IsWeightedCoeffOn (originCube (d := d) 1) (whCoeff d q t) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  refine scalar_weightedCoeffOn _ (measurable_whWeight d q t) ?_ (whWeight_integrable hβ)
    (whInv_integrable hβ hβd)
  have h0 : ∀ᵐ x ∂(volume.restrict (originCube (d := d) 1)), x ≠ 0 := by
    apply ae_restrict_of_ae
    exact (Set.countable_singleton (0 : Vec d)).ae_notMem volume
  filter_upwards [h0, ae_restrict_mem measurableSet_originCube] with x hx0 hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hρpos : 0 < euclidNorm x := hxpos.trans_le (norm_le_euclidNorm x)
  rw [whField_eq hρpos (norm_lt_R_of_mem hx)]
  exact whA_pos hρpos (norm_lt_R_of_mem hx)

end

end CoarseDeGiorgi.SharpnessExamples
