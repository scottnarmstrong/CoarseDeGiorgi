import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessLower
import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessAnalysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Positivity of the lower moment of the weak Harnack field -/

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem whNear_total_le {d : ℕ} [NeZero d] {β L : ℝ} (hβd : β < d) (hL : 0 ≤ L) :
    ∫ x in originCube (d := d) 1, whNear β (Real.exp (-L)) ‖x‖ ≤
      polarConst d * ((1 + L) ^ (-3 : ℝ) *
        (Real.exp (-L) ^ ((d : ℝ) - β) / ((d : ℝ) - β))) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h0 : 0 < Real.exp (-L) := Real.exp_pos _
  have h1 : Real.exp (-L) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  obtain ⟨hi, hb⟩ := near_integral hd hβd h0 h1
  have hint : Integrable (fun x : Vec d => whNear β (Real.exp (-L)) ‖x‖) :=
    (integrable_polar_pi (d := d) (f := whNear β (Real.exp (-L)))).2 hi
  have hnn : ∀ x : Vec d, 0 ≤ whNear β (Real.exp (-L)) ‖x‖ :=
    fun x => whNear_nonneg β _ (norm_nonneg x) h1
  calc ∫ x in originCube (d := d) 1, whNear β (Real.exp (-L)) ‖x‖
      ≤ ∫ x : Vec d, whNear β (Real.exp (-L)) ‖x‖ :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
    _ = polarConst d * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * whNear β (Real.exp (-L)) y :=
        polar_pi _
    _ ≤ polarConst d * ((1 - Real.log (Real.exp (-L))) ^ (-3 : ℝ) *
          (Real.exp (-L) ^ ((d : ℝ) - β) / ((d : ℝ) - β))) :=
        mul_le_mul_of_nonneg_left hb (polarConst_nonneg d)
    _ = _ := by rw [Real.log_exp]; ring_nf

theorem whFar_total_le {d : ℕ} [NeZero d] {β q L : ℝ} (hq : 0 < q) (hγ : (d : ℝ) < β * q)
    (hL : 0 ≤ L) :
    ∫ x in originCube (d := d) 1, whFar β (Real.exp (-L)) ‖x‖ ^ q ≤
      polarConst d * (((1 + L / 2) ^ (-3 * q) * Real.exp (-L) ^ (-(β * q - d)) +
        Real.exp (-(L / 2)) ^ (-(β * q - d))) / (β * q - d)) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h0 : 0 < Real.exp (-L) := Real.exp_pos _
  have hhs : Real.exp (-L) ≤ Real.exp (-(L / 2)) := by
    rw [Real.exp_le_exp]; linarith
  have hs1 : Real.exp (-(L / 2)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  obtain ⟨hi, hb⟩ := far_integral (d := d) (β := β) hd hq hγ h0 hhs hs1
  have hint : Integrable (fun x : Vec d => whFar β (Real.exp (-L)) ‖x‖ ^ q) :=
    (integrable_polar_pi (d := d) (f := fun r => whFar β (Real.exp (-L)) r ^ q)).2 hi
  have hnn : ∀ x : Vec d, 0 ≤ whFar β (Real.exp (-L)) ‖x‖ ^ q :=
    fun x => Real.rpow_nonneg (whFar_nonneg β _ (norm_nonneg x)) _
  calc ∫ x in originCube (d := d) 1, whFar β (Real.exp (-L)) ‖x‖ ^ q
      ≤ ∫ x : Vec d, whFar β (Real.exp (-L)) ‖x‖ ^ q :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
    _ = polarConst d * ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * whFar β (Real.exp (-L)) y ^ q :=
        polar_pi (fun r => whFar β (Real.exp (-L)) r ^ q)
    _ ≤ polarConst d * (((1 - Real.log (Real.exp (-(L / 2)))) ^ (-3 * q) *
          Real.exp (-L) ^ (-(β * q - d)) + Real.exp (-(L / 2)) ^ (-(β * q - d))) /
          (β * q - d)) := mul_le_mul_of_nonneg_left hb (polarConst_nonneg d)
    _ = _ := by rw [Real.log_exp]; ring_nf

theorem whBeta_mul {d : ℕ} {q t : ℝ} (hq : q ≠ 0) :
    whBeta d q t * q - d = 2 * t * q := by
  unfold whBeta
  field_simp
  ring

theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem whLower_level_bound {d : ℕ} [NeZero d] {q t : ℝ} (hq : 1 < q) (ht : 0 < t)
    (hβ : 0 < whBeta d q t) (hβd : whBeta d q t < d)
    (ha : IsWeightedCoeffOn (originCube (d := d) 1) (whCoeff d q t)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, lowerCellAverage (whCoeff d q t) ha k q ≤
      K * (1 + (k : ℝ)) ^ (-3 * q) * Real.exp (2 * t * q * ((k : ℝ) * Real.log 3)) := by
  have hq0 : 0 < q := by linarith
  have hγ : 0 < whBeta d q t * q - d := by rw [whBeta_mul hq0.ne']; positivity
  have hF : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  obtain ⟨K, hK0, hK⟩ := level_final (q := q) (β := whBeta d q t) (γ := whBeta d q t * q - d)
    (C1 := polarConst d) (F := (d.factorial : ℝ)) (dr := (d : ℝ)) hq.le (by linarith) hF rfl hγ
    (polarConst_nonneg d)
  refine ⟨K, hK0, fun k => ?_⟩
  set L : ℝ := (k : ℝ) * Real.log 3 with hL
  have hL0 : 0 ≤ L := mul_nonneg (Nat.cast_nonneg _) (by linarith [one_le_log_three])
  have hkL : (k : ℝ) ≤ L := by
    rw [hL]; nlinarith [one_le_log_three, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h0 : 0 < Real.exp (-L) := Real.exp_pos _
  have h1 : Real.exp (-L) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have hlev := whLower_level_le hβ hβd hq.le h0 h1 ha k
  have hN : ((triangulation (d := d) k).card : ℝ) = (d.factorial : ℝ) * Real.exp ((d : ℝ) * L) := by
    rw [triangulation_card]
    push_cast
    rw [show ((d : ℝ) * L) = Real.log 3 * ((k * d : ℕ) : ℝ) by rw [hL]; push_cast; ring,
      Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
  have hI1 := whNear_total_le (d := d) hβd hL0
  have hI2 := whFar_total_le (d := d) (β := whBeta d q t) hq0 (by linarith) hL0
  have hI1nn : 0 ≤ ∫ x in originCube (d := d) 1, whNear (whBeta d q t) (Real.exp (-L)) ‖x‖ :=
    integral_nonneg (fun x => whNear_nonneg _ _ (norm_nonneg x) h1)
  have hI2nn : 0 ≤ ∫ x in originCube (d := d) 1, whFar (whBeta d q t) (Real.exp (-L)) ‖x‖ ^ q :=
    integral_nonneg (fun x => Real.rpow_nonneg (whFar_nonneg _ _ (norm_nonneg x)) _)
  have hfin := hK L hL0 _ _ hI1nn hI2nn hI1 hI2
  rw [hN] at hlev
  have hγ2 : whBeta d q t * q - d = 2 * t * q := whBeta_mul hq0.ne'
  rw [hγ2] at hfin
  refine hlev.trans (hfin.trans ?_)
  have hu : 0 < 1 + (k : ℝ) := by positivity
  have : (1 + L) ^ (-3 * q) ≤ (1 + (k : ℝ)) ^ (-3 * q) :=
    Real.rpow_le_rpow_of_nonpos hu (by linarith) (by nlinarith)
  have hE : 0 ≤ Real.exp (2 * t * q * L) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hK0) hE

theorem whLowerMoment_pos {d : ℕ} [NeZero d] {q t : ℝ} (hq : 1 < q) (ht : 0 < t)
    (hβ : 0 < whBeta d q t) (hβd : whBeta d q t < d)
    (ha : IsWeightedCoeffOn (originCube (d := d) 1) (whCoeff d q t)) :
    0 < lowerMoment (whCoeff d q t) ha t q ht hq.le := by
  have hq0 : 0 < q := by linarith
  obtain ⟨K, hK0, hK⟩ := whLower_level_bound hq ht hβ hβd ha
  set c : ℕ → ℝ := fun k => K ^ (1 / (2 * q)) * (1 + (k : ℝ)) ^ (-(3 / 2 : ℝ)) with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => mul_nonneg (Real.rpow_nonneg hK0 _)
    (Real.rpow_nonneg (by positivity) _)
  have hcs : Summable c := by
    have h1 := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
    have h2 := h1.mul_left (K ^ (1 / (2 * q)))
    refine h2.congr (fun k => ?_)
    simp only [hc]
    rw [Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity), add_comm]
    simp
  have hterm : ∀ k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
      (ENNReal.ofReal (lowerCellAverage (whCoeff d q t) ha k q)).rpow (1 / (2 * q)) ≤
      ENNReal.ofReal (c k) := by
    intro k
    set B : ℝ := K * (1 + (k : ℝ)) ^ (-3 * q) * Real.exp (2 * t * q * ((k : ℝ) * Real.log 3))
      with hB
    have hu : 0 < 1 + (k : ℝ) := by positivity
    have hB0 : 0 ≤ B := by positivity
    have hr : 0 ≤ 1 / (2 * q) := by positivity
    have h1 : (ENNReal.ofReal (lowerCellAverage (whCoeff d q t) ha k q)).rpow (1 / (2 * q)) ≤
        ENNReal.ofReal (B ^ (1 / (2 * q))) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hB0 hr]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hK k)) hr
    have h2 : Real.rpow 3 (-((k : ℝ) * t)) * B ^ (1 / (2 * q)) = c k := by
      have a1 : ((1 + (k : ℝ)) ^ (-3 * q)) ^ (1 / (2 * q)) = (1 + (k : ℝ)) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_mul hu.le]
        congr 1
        field_simp
      have a2 : Real.exp (2 * t * q * ((k : ℝ) * Real.log 3)) ^ (1 / (2 * q)) =
          Real.exp (t * ((k : ℝ) * Real.log 3)) := by
        rw [rpow_exp']
        congr 1
        field_simp
      have e1 : B ^ (1 / (2 * q)) = K ^ (1 / (2 * q)) * (1 + (k : ℝ)) ^ (-(3 / 2 : ℝ)) *
          Real.exp (t * ((k : ℝ) * Real.log 3)) := by
        rw [hB, Real.mul_rpow (mul_nonneg hK0 (Real.rpow_nonneg hu.le _)) (Real.exp_pos _).le,
          Real.mul_rpow hK0 (Real.rpow_nonneg hu.le _), a1, a2]
      have e2 : Real.rpow 3 (-((k : ℝ) * t)) = Real.exp (-(t * ((k : ℝ) * Real.log 3))) := by
        change (3 : ℝ) ^ (-((k : ℝ) * t)) = _
        rw [Real.rpow_def_of_pos (by norm_num)]
        congr 1; ring
      rw [e1, e2, hc]
      have : Real.exp (-(t * ((k : ℝ) * Real.log 3))) * Real.exp (t * ((k : ℝ) * Real.log 3)) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-(t * ((k : ℝ) * Real.log 3))) * (K ^ (1 / (2 * q)) *
            (1 + (k : ℝ)) ^ (-(3 / 2 : ℝ)) * Real.exp (t * ((k : ℝ) * Real.log 3)))
          = (K ^ (1 / (2 * q)) * (1 + (k : ℝ)) ^ (-(3 / 2 : ℝ))) *
            (Real.exp (-(t * ((k : ℝ) * Real.log 3))) * Real.exp (t * ((k : ℝ) * Real.log 3))) := by
            ring
        _ = _ := by rw [this, mul_one]
    calc ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (ENNReal.ofReal (lowerCellAverage (whCoeff d q t) ha k q)).rpow (1 / (2 * q))
        ≤ ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) * ENNReal.ofReal (B ^ (1 / (2 * q))) :=
          mul_le_mul_right h1 _
      _ = ENNReal.ofReal (c k) := by
          have hp : 0 ≤ Real.rpow 3 (-((k : ℝ) * t)) := Real.rpow_nonneg (by norm_num) _
          rw [← ENNReal.ofReal_mul hp, h2]
  have hsum : (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
      (ENNReal.ofReal (lowerCellAverage (whCoeff d q t) ha k q)).rpow (1 / (2 * q))) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) (hcs.tsum_ofReal_lt_top)
  unfold lowerMoment
  have hx : ENNReal.ofReal (1 - Real.rpow 3 (-t)) * (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
      (ENNReal.ofReal (lowerCellAverage (whCoeff d q t) ha k q)).rpow (1 / (2 * q))) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum
  have key : ∀ y : ℝ≥0∞, y ≠ ⊤ → 0 < y.rpow (-2) := by
    intro y hy
    change 0 < y ^ (-2 : ℝ)
    rw [ENNReal.rpow_neg, ENNReal.inv_pos]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hy
  exact key _ hx.ne

end

end CoarseDeGiorgi.SharpnessExamples
