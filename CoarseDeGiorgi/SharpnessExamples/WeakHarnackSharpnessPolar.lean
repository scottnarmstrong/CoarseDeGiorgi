import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessField
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Radial integrals for the weak Harnack sharpness example

Polar coordinates in the supremum norm of `Vec d`, and the radial majorant
`ω(r) = r^{-β} (1 - log r)^{-3}` split at a radius `h`.
-/

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem polar_pi {d : ℕ} [NeZero d] (f : ℝ → ℝ) :
    ∫ x : Vec d, f ‖x‖ = d * volume.real (Metric.ball (0 : Vec d) 1) *
      ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * f y := by
  have := integral_fun_norm_addHaar (volume : Measure (Vec d)) f
  rw [Module.finrank_fin_fun] at this
  simpa only [nsmul_eq_mul, smul_eq_mul, mul_assoc] using this

theorem integrable_polar_pi {d : ℕ} [NeZero d] {f : ℝ → ℝ} :
    Integrable (fun x : Vec d => f ‖x‖) ↔ IntegrableOn (fun y => y ^ (d - 1) * f y) (Ioi 0) := by
  have := integrable_fun_norm_addHaar (volume : Measure (Vec d)) (f := f)
  rw [Module.finrank_fin_fun] at this
  simpa only [smul_eq_mul] using this

/-- The polar constant `d |B(0,1)|`. -/
def polarConst (d : ℕ) : ℝ := d * volume.real (Metric.ball (0 : Vec d) 1)

theorem polarConst_nonneg (d : ℕ) : 0 ≤ polarConst d :=
  mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg

/-- The radial majorant `r^{-β} (1 - log r)^{-3}`. -/
def whOmega (β r : ℝ) : ℝ := r ^ (-β) * (1 - Real.log r) ^ (-3 : ℝ)

/-- The part of the majorant inside the radius `h`. -/
def whNear (β h r : ℝ) : ℝ := if r < h then whOmega β r else 0

/-- The part of the majorant between the radii `h` and `1`. -/
def whFar (β h r : ℝ) : ℝ := if h ≤ r ∧ r < 1 then whOmega β r else 0

theorem measurable_whOmega (β : ℝ) : Measurable (whOmega β) := by
  unfold whOmega
  fun_prop

theorem measurable_whNear (β h : ℝ) : Measurable (whNear β h) := by
  unfold whNear
  exact Measurable.ite measurableSet_Iio (measurable_whOmega β) measurable_const

theorem measurable_whFar (β h : ℝ) : Measurable (whFar β h) := by
  unfold whFar
  exact Measurable.ite ((measurableSet_Ici.inter measurableSet_Iio)) (measurable_whOmega β)
    measurable_const

theorem whOmega_nonneg (β : ℝ) {r : ℝ} (hr : 0 ≤ r) (h1 : r ≤ 1) : 0 ≤ whOmega β r := by
  unfold whOmega
  have : 0 ≤ 1 - Real.log r := by
    rcases hr.eq_or_lt with h | h
    · subst h; simp
    · have := Real.log_nonpos hr h1; linarith
  exact mul_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg this _)

/-- On `(0, h)` the logarithmic factor is at least `c = 1 - log h`. -/
theorem whOmega_le_near {β h r : ℝ} (hr : 0 < r) (hrh : r < h) (h1 : h ≤ 1) :
    whOmega β r ≤ (1 - Real.log h) ^ (-3 : ℝ) * r ^ (-β) := by
  unfold whOmega
  have hl : Real.log r ≤ Real.log h := Real.log_le_log hr hrh.le
  have hc : 0 < 1 - Real.log h := by
    have := Real.log_nonpos (hr.trans hrh).le h1
    linarith
  have : (1 - Real.log r) ^ (-3 : ℝ) ≤ (1 - Real.log h) ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hc (by linarith) (by norm_num)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hr.le _)

theorem natpow_mul_rpow {d : ℕ} (hd : 1 ≤ d) {y : ℝ} (hy : 0 < y) (e : ℝ) :
    y ^ (d - 1) * y ^ e = y ^ ((d : ℝ) - 1 + e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hy, Nat.cast_sub hd]
  simp

theorem near_integral {d : ℕ} (hd : 1 ≤ d) {β h : ℝ} (hβ : β < d) (h0 : 0 < h) (h1 : h ≤ 1) :
    IntegrableOn (fun y => y ^ (d - 1) * whNear β h y) (Ioi 0) ∧
    ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * whNear β h y ≤
      (1 - Real.log h) ^ (-3 : ℝ) * (h ^ ((d : ℝ) - β) / ((d : ℝ) - β)) := by
  set c := (1 - Real.log h) ^ (-3 : ℝ) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by linarith [Real.log_nonpos h0.le h1]) _
  let g : ℝ → ℝ := fun y => c * y ^ ((d : ℝ) - 1 - β)
  have hgi : IntegrableOn g (Ioc 0 h) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := h)
      (r := (d : ℝ) - 1 - β) (by linarith)).const_mul c
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h0.le).1 this
  have hpt : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) * whNear β h y ≤ (Ioc 0 h).indicator g y := by
    intro y hy
    have hy0 : 0 < y := hy
    unfold whNear
    by_cases hyh : y < h
    · simp only [hyh, ↓reduceIte]
      rw [indicator_of_mem (show y ∈ Ioc 0 h from ⟨hy0, hyh.le⟩)]
      calc y ^ (d - 1) * whOmega β y ≤ y ^ (d - 1) * (c * y ^ (-β)) :=
            mul_le_mul_of_nonneg_left (whOmega_le_near hy0 hyh h1) (by positivity)
        _ = c * y ^ ((d : ℝ) - 1 - β) := by
            rw [mul_left_comm, natpow_mul_rpow hd hy0]
            ring_nf
    · simp only [hyh, ↓reduceIte, mul_zero]
      exact indicator_nonneg (fun z hz => mul_nonneg hc0 (Real.rpow_nonneg hz.1.le _)) y
  have hmeas : AEStronglyMeasurable (fun y : ℝ => y ^ (d - 1) * whNear β h y)
      (volume.restrict (Ioi 0)) :=
    ((measurable_id.pow_const _).mul (measurable_whNear β h)).aestronglyMeasurable
  have hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ y ^ (d - 1) * whNear β h y := by
    intro y hy
    have hy0 : 0 < y := hy
    unfold whNear
    by_cases hyh : y < h
    · simp only [hyh, ↓reduceIte]
      exact mul_nonneg (by positivity) (whOmega_nonneg β hy0.le (hyh.le.trans h1))
    · simp only [hyh, ↓reduceIte, mul_zero]; exact le_rfl
  have hgind : Integrable ((Ioc 0 h).indicator g) (volume.restrict (Ioi 0)) := by
    have : Integrable ((Ioc 0 h).indicator g) volume := (integrable_indicator_iff measurableSet_Ioc).2 hgi
    exact this.restrict
  refine ⟨?_, ?_⟩
  · refine hgind.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_of_nonneg (hnn y hy)]
    exact hpt y hy
  · have hint : ∫ y in Ioi (0 : ℝ), (Ioc 0 h).indicator g y = c * (h ^ ((d : ℝ) - β) / ((d : ℝ) - β)) := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
      have : Ioc 0 h ∩ Ioi 0 = Ioc (0 : ℝ) h := by
        ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
        · exact fun ⟨a, _⟩ => a
        · exact fun a => ⟨a, a.1⟩
      rw [this, ← intervalIntegral.integral_of_le h0.le, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith))]
      have e1 : (d : ℝ) - 1 - β + 1 = d - β := by ring
      rw [e1, Real.zero_rpow (by linarith), sub_zero]
    rw [← hint]
    refine integral_mono_of_nonneg ?_ hgind ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using hnn y hy
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using hpt y hy

theorem whOmega_rpow (β : ℝ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (p : ℝ) :
    whOmega β y ^ p = y ^ (-β * p) * (1 - Real.log y) ^ (-3 * p) := by
  have h1 : 0 ≤ 1 - Real.log y := by linarith [Real.log_nonpos hy.le hy1]
  unfold whOmega
  rw [Real.mul_rpow (Real.rpow_nonneg hy.le _) (Real.rpow_nonneg h1 _),
    ← Real.rpow_mul hy.le, ← Real.rpow_mul h1]

theorem natpow_whOmega_rpow {d : ℕ} (hd : 1 ≤ d) (β : ℝ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (p : ℝ) :
    y ^ (d - 1) * whOmega β y ^ p =
      y ^ ((d : ℝ) - 1 - β * p) * (1 - Real.log y) ^ (-3 * p) := by
  rw [whOmega_rpow β hy hy1, ← mul_assoc, natpow_mul_rpow hd hy]
  ring_nf

theorem far_integral {d : ℕ} (hd : 1 ≤ d) {β q h s : ℝ} (hq : 0 < q) (hγ : (d : ℝ) < β * q)
    (h0 : 0 < h) (hhs : h ≤ s) (hs1 : s ≤ 1) :
    IntegrableOn (fun y => y ^ (d - 1) * whFar β h y ^ q) (Ioi 0) ∧
    ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * whFar β h y ^ q ≤
      ((1 - Real.log s) ^ (-3 * q) * h ^ (-(β * q - d)) + s ^ (-(β * q - d))) / (β * q - d) := by
  set γ := β * q - d with hγdef
  have hγ0 : 0 < γ := by linarith
  have hs0 : 0 < s := h0.trans_le hhs
  set K := (1 - Real.log s) ^ (-3 * q) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by linarith [Real.log_nonpos hs0.le hs1]) _
  let g1 : ℝ → ℝ := fun y => K * y ^ (-1 - γ)
  let g2 : ℝ → ℝ := fun y => y ^ (-1 - γ)
  have hint1 : IntegrableOn g1 (Icc h s) := by
    have h3 : IntervalIntegrable (fun y : ℝ => y ^ (-1 - γ)) volume h s :=
      intervalIntegral.intervalIntegrable_rpow (a := h) (b := s) (r := -1 - γ)
        (Or.inr (by rw [uIcc_of_le hhs]; exact fun hh => absurd hh.1 (not_le.2 h0)))
    have := h3.const_mul K
    have h2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hhs).1 this
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h2
  have hint2 : IntegrableOn g2 (Ioc s 1) := by
    have : IntervalIntegrable (fun y : ℝ => y ^ (-1 - γ)) volume s 1 :=
      intervalIntegral.intervalIntegrable_rpow (a := s) (b := 1) (r := -1 - γ)
        (Or.inr (by rw [uIcc_of_le hs1]; exact fun hh => absurd hh.1 (not_le.2 hs0)))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hs1).1 this
  let G : ℝ → ℝ := (Icc h s).indicator g1 + (Ioc s 1).indicator g2
  have hGi : Integrable G (volume.restrict (Ioi 0)) := by
    refine Integrable.add ?_ ?_
    · exact Integrable.restrict (s := Ioi (0 : ℝ)) ((integrable_indicator_iff measurableSet_Icc).2 hint1)
    · exact Integrable.restrict (s := Ioi (0 : ℝ)) ((integrable_indicator_iff measurableSet_Ioc).2 hint2)
  have hexp : ∀ y : ℝ, 0 < y → y ^ (d - 1) * whFar β h y ^ q ≤ G y ∧
      0 ≤ y ^ (d - 1) * whFar β h y ^ q := by
    intro y hy0
    have hnn : 0 ≤ y ^ (d - 1) * whFar β h y ^ q := by
      unfold whFar
      by_cases hc : h ≤ y ∧ y < 1
      · simp only [hc, and_self, ↓reduceIte]
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (whOmega_nonneg β hy0.le hc.2.le) _)
      · simp only [hc, ↓reduceIte]
        rw [Real.zero_rpow hq.ne', mul_zero]
    refine ⟨?_, hnn⟩
    unfold whFar
    by_cases hc : h ≤ y ∧ y < 1
    · simp only [hc, and_self, ↓reduceIte]
      rw [natpow_whOmega_rpow hd β hy0 hc.2.le q]
      have e : (d : ℝ) - 1 - β * q = -1 - γ := by rw [hγdef]; ring
      rw [e]
      have hl : 0 ≤ 1 - Real.log y := by linarith [Real.log_nonpos hy0.le hc.2.le]
      by_cases hys : y ≤ s
      · have hm : y ∈ Icc h s := ⟨hc.1, hys⟩
        have hnm : y ∉ Ioc s 1 := fun hh => absurd hh.1 (not_lt.2 hys)
        simp only [G, Pi.add_apply, indicator_of_mem hm, indicator_of_notMem hnm, add_zero, g1]
        have : (1 - Real.log y) ^ (-3 * q) ≤ K := by
          have hl2 : 1 - Real.log s ≤ 1 - Real.log y := by
            have := Real.log_le_log hy0 hys; linarith
          exact Real.rpow_le_rpow_of_nonpos (by linarith [Real.log_nonpos hs0.le hs1]) hl2
            (by nlinarith)
        calc y ^ (-1 - γ) * (1 - Real.log y) ^ (-3 * q) ≤ y ^ (-1 - γ) * K :=
              mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hy0.le _)
          _ = _ := mul_comm _ _
      · have hm : y ∈ Ioc s 1 := ⟨not_le.1 hys, hc.2.le⟩
        have hnm : y ∉ Icc h s := fun hh => absurd hh.2 hys
        simp only [G, Pi.add_apply, indicator_of_mem hm, indicator_of_notMem hnm, zero_add, g2]
        have : (1 - Real.log y) ^ (-3 * q) ≤ 1 := by
          apply Real.rpow_le_one_of_one_le_of_nonpos _ (by nlinarith)
          linarith [Real.log_nonpos hy0.le hc.2.le]
        calc y ^ (-1 - γ) * (1 - Real.log y) ^ (-3 * q) ≤ y ^ (-1 - γ) * 1 :=
              mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hy0.le _)
          _ = _ := mul_one _
    · simp only [hc, ↓reduceIte]
      rw [Real.zero_rpow hq.ne', mul_zero]
      have hn1 : 0 ≤ (Icc h s).indicator g1 y :=
        indicator_nonneg (fun z hz => mul_nonneg hK0 (Real.rpow_nonneg (h0.trans_le hz.1).le _)) y
      have hn2 : 0 ≤ (Ioc s 1).indicator g2 y :=
        indicator_nonneg (fun z hz => Real.rpow_nonneg (hs0.trans hz.1).le _) y
      exact add_nonneg hn1 hn2
  have hmeas : AEStronglyMeasurable (fun y : ℝ => y ^ (d - 1) * whFar β h y ^ q)
      (volume.restrict (Ioi 0)) :=
    ((measurable_id.pow_const _).mul ((measurable_whFar β h).pow_const q)).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine hGi.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have := hexp y hy
    rw [Real.norm_of_nonneg this.2]
    exact this.1
  · have hI1 : ∫ y in Ioi (0 : ℝ), (Icc h s).indicator g1 y =
        K * ((s ^ (-γ) - h ^ (-γ)) / (-γ)) := by
      rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
      have : Icc h s ∩ Ioi 0 = Icc h s := by
        ext y; simp only [mem_inter_iff, mem_Icc, mem_Ioi]; constructor
        · exact fun ⟨a, _⟩ => a
        · exact fun a => ⟨a, h0.trans_le a.1⟩
      rw [this, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hhs]
      simp only [g1]
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le hhs]; exact fun hh => absurd hh.1 (not_le.2 h0)⟩)]
      have e1 : -1 - γ + 1 = -γ := by ring
      rw [e1]
    have hI2 : ∫ y in Ioi (0 : ℝ), (Ioc s 1).indicator g2 y = (1 ^ (-γ) - s ^ (-γ)) / (-γ) := by
      rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
      have : Ioc s 1 ∩ Ioi 0 = Ioc s 1 := by
        ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
        · exact fun ⟨a, _⟩ => a
        · exact fun a => ⟨a, hs0.trans a.1⟩
      rw [this, ← intervalIntegral.integral_of_le hs1]
      simp only [g2]
      rw [integral_rpow (Or.inr ⟨by linarith, by
        rw [uIcc_of_le hs1]; exact fun hh => absurd hh.1 (not_le.2 hs0)⟩)]
      have e1 : -1 - γ + 1 = -γ := by ring
      rw [e1]
    have hmain : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * whFar β h y ^ q ≤ ∫ y in Ioi (0 : ℝ), G y := by
      refine integral_mono_of_nonneg ?_ hGi ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using (hexp y hy).2
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using (hexp y hy).1
    have hsum : ∫ y in Ioi (0 : ℝ), G y = K * ((s ^ (-γ) - h ^ (-γ)) / (-γ)) +
        (1 ^ (-γ) - s ^ (-γ)) / (-γ) := by
      simp only [G, Pi.add_apply]
      rw [integral_add (Integrable.restrict (s := Ioi (0 : ℝ))
          ((integrable_indicator_iff measurableSet_Icc).2 hint1))
        (Integrable.restrict (s := Ioi (0 : ℝ))
          ((integrable_indicator_iff measurableSet_Ioc).2 hint2)), hI1, hI2]
    refine hmain.trans (hsum.le.trans ?_)
    rw [Real.one_rpow]
    have hs' : 0 < s ^ (-γ) := Real.rpow_pos_of_pos hs0 _
    have hh' : 0 < h ^ (-γ) := Real.rpow_pos_of_pos h0 _
    have hsh : s ^ (-γ) ≤ h ^ (-γ) := Real.rpow_le_rpow_of_nonpos h0 hhs (by linarith)
    have e : K * ((s ^ (-γ) - h ^ (-γ)) / (-γ)) + (1 - s ^ (-γ)) / (-γ) =
        (K * (h ^ (-γ) - s ^ (-γ)) + (s ^ (-γ) - 1)) / γ := by
      field_simp
      ring
    rw [e]
    apply div_le_div_of_nonneg_right _ hγ0.le
    nlinarith [mul_nonneg hK0 hs'.le]

end

end CoarseDeGiorgi.SharpnessExamples
