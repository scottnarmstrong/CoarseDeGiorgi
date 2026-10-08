module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Elementary real analysis for the weak Harnack level bound -/

@[expose] public section

open Real

namespace CoarseDeGiorgi.SharpnessExamples

theorem rpow_exp' (a b : ℝ) : (Real.exp a) ^ b = Real.exp (a * b) := (Real.exp_mul a b).symm

/-- A polynomial factor is dominated by an exponential. -/
theorem exp_bound {γ q : ℝ} (hγ : 0 < γ) (hq : 0 < q) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧ ∀ L : ℝ, 0 ≤ L → (1 + L) ^ (3 * q) ≤ Kb * Real.exp (γ * L / 2) := by
  set a : ℝ := γ / (6 * q) with ha
  have ha0 : 0 < a := by positivity
  set m : ℝ := max 1 a⁻¹ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hma : 1 ≤ m * a := by
    have : a⁻¹ ≤ m := le_max_right _ _
    calc (1 : ℝ) = a⁻¹ * a := (inv_mul_cancel₀ ha0.ne').symm
      _ ≤ m * a := mul_le_mul_of_nonneg_right this ha0.le
  refine ⟨m ^ (3 * q), by positivity, fun L hL => ?_⟩
  have h1 : 1 + L ≤ m * Real.exp (a * L) := by
    have := Real.add_one_le_exp (a * L)
    nlinarith
  have hpos : 0 ≤ 1 + L := by linarith
  calc (1 + L) ^ (3 * q) ≤ (m * Real.exp (a * L)) ^ (3 * q) :=
        Real.rpow_le_rpow hpos h1 (by positivity)
    _ = m ^ (3 * q) * Real.exp (γ * L / 2) := by
        rw [Real.mul_rpow (by linarith) (Real.exp_pos _).le, rpow_exp']
        congr 2
        rw [ha]
        field_simp
        ring

theorem exp_le_of_exp_bound {γ q Kb : ℝ} (hb : ∀ L : ℝ, 0 ≤ L →
    (1 + L) ^ (3 * q) ≤ Kb * Real.exp (γ * L / 2)) {L : ℝ} (hL : 0 ≤ L) :
    Real.exp (γ * L / 2) ≤ Kb * (1 + L) ^ (-3 * q) * Real.exp (γ * L) := by
  have hu : 0 < 1 + L := by linarith
  have h1 := hb L hL
  have h2 : (1 + L) ^ (-3 * q) * (1 + L) ^ (3 * q) = 1 := by
    rw [← Real.rpow_add hu]; simp
  have h3 : Real.exp (γ * L) = Real.exp (γ * L / 2) * Real.exp (γ * L / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos : 0 ≤ (1 + L) ^ (-3 * q) := Real.rpow_nonneg hu.le _
  calc Real.exp (γ * L / 2) = (1 + L) ^ (-3 * q) * (1 + L) ^ (3 * q) * Real.exp (γ * L / 2) := by
        rw [h2, one_mul]
    _ ≤ (1 + L) ^ (-3 * q) * (Kb * Real.exp (γ * L / 2)) * Real.exp (γ * L / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left h1 hpos
    _ = Kb * (1 + L) ^ (-3 * q) * Real.exp (γ * L) := by rw [h3]; ring

theorem level_final {q β γ C1 F dr : ℝ} (hq : 1 ≤ q) (hD : 0 < dr - β) (hF : 0 < F)
    (hγ : γ = β * q - dr) (hγ0 : 0 < γ) (hC1 : 0 ≤ C1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, 0 ≤ L → ∀ I1 I2 : ℝ, 0 ≤ I1 → 0 ≤ I2 →
      I1 ≤ C1 * ((1 + L) ^ (-3 : ℝ) * (Real.exp (-L) ^ (dr - β) / (dr - β))) →
      I2 ≤ C1 * (((1 + L / 2) ^ (-3 * q) * Real.exp (-L) ^ (-γ) +
        Real.exp (-(L / 2)) ^ (-γ)) / γ) →
      2 ^ q * ((F * Real.exp (dr * L)) ^ (q - 1) * I1 ^ q + I2) ≤
        K * (1 + L) ^ (-3 * q) * Real.exp (γ * L) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨Kb, hKb0, hKb⟩ := exp_bound hγ0 hq0
  set KA : ℝ := F ^ (q - 1) * C1 ^ q / (dr - β) ^ q with hKA
  have hKA0 : 0 ≤ KA := by positivity
  set KB : ℝ := C1 / γ * (2 ^ (3 * q) + Kb) with hKB
  have hKB0 : 0 ≤ KB := by positivity
  refine ⟨2 ^ q * (KA + KB), by positivity, fun L hL I1 I2 hI1 hI2 hb1 hb2 => ?_⟩
  have hu : 0 < 1 + L := by linarith
  have hupos : 0 ≤ (1 + L) ^ (-3 * q) := Real.rpow_nonneg hu.le _
  -- first term
  have hT1 : (F * Real.exp (dr * L)) ^ (q - 1) * I1 ^ q ≤ KA * (1 + L) ^ (-3 * q) *
      Real.exp (γ * L) := by
    have hI1q : I1 ^ q ≤ (C1 * ((1 + L) ^ (-3 : ℝ) * (Real.exp (-L) ^ (dr - β) / (dr - β)))) ^ q :=
      Real.rpow_le_rpow hI1 hb1 hq0.le
    have hexpand : (C1 * ((1 + L) ^ (-3 : ℝ) * (Real.exp (-L) ^ (dr - β) / (dr - β)))) ^ q =
        C1 ^ q * ((1 + L) ^ (-3 * q) * (Real.exp (-(L * (dr - β) * q)) / (dr - β) ^ q)) := by
      have e1 : (Real.exp (-L) ^ (dr - β)) ^ q = Real.exp (-(L * (dr - β) * q)) := by
        rw [← Real.rpow_mul (Real.exp_pos _).le, rpow_exp']
        congr 1; ring
      have e2 : ((1 + L) ^ (-3 : ℝ)) ^ q = (1 + L) ^ (-3 * q) := by
        rw [← Real.rpow_mul hu.le]
      rw [Real.mul_rpow hC1 (mul_nonneg (Real.rpow_nonneg hu.le _)
          (div_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) hD.le)),
        Real.mul_rpow (Real.rpow_nonneg hu.le _)
          (div_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) hD.le),
        Real.div_rpow (Real.rpow_nonneg (Real.exp_pos _).le _) hD.le, e1, e2]
    have hN : (F * Real.exp (dr * L)) ^ (q - 1) = F ^ (q - 1) * Real.exp (dr * L * (q - 1)) := by
      rw [Real.mul_rpow hF.le (Real.exp_pos _).le, rpow_exp']
    calc (F * Real.exp (dr * L)) ^ (q - 1) * I1 ^ q
        ≤ (F * Real.exp (dr * L)) ^ (q - 1) *
          (C1 ^ q * ((1 + L) ^ (-3 * q) * (Real.exp (-(L * (dr - β) * q)) / (dr - β) ^ q))) := by
          rw [← hexpand]
          exact mul_le_mul_of_nonneg_left hI1q (Real.rpow_nonneg (mul_nonneg hF.le
            (Real.exp_pos _).le) _)
      _ = KA * (1 + L) ^ (-3 * q) * (Real.exp (dr * L * (q - 1)) * Real.exp (-(L * (dr - β) * q))) := by
          rw [hN, hKA]; ring
      _ = KA * (1 + L) ^ (-3 * q) * Real.exp (γ * L) := by
          rw [← Real.exp_add]; congr 2; rw [hγ]; ring
  -- second term
  have hT2 : I2 ≤ KB * (1 + L) ^ (-3 * q) * Real.exp (γ * L) := by
    have e1 : Real.exp (-L) ^ (-γ) = Real.exp (γ * L) := by
      rw [rpow_exp']; congr 1; ring
    have e2 : Real.exp (-(L / 2)) ^ (-γ) = Real.exp (γ * L / 2) := by
      rw [rpow_exp']; congr 1; ring
    rw [e1, e2] at hb2
    have hh1 : (1 + L / 2) ^ (-3 * q) ≤ 2 ^ (3 * q) * (1 + L) ^ (-3 * q) := by
      have hx : 0 < (1 + L) / 2 := by positivity
      have hxy : (1 + L) / 2 ≤ 1 + L / 2 := by linarith
      have := Real.rpow_le_rpow_of_nonpos hx hxy (by nlinarith : -3 * q ≤ 0)
      refine this.trans (le_of_eq ?_)
      rw [Real.div_rpow hu.le (by norm_num), show (-3 * q) = -(3 * q) by ring, Real.rpow_neg
        (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg hu.le]
      field_simp
    have hh2 := exp_le_of_exp_bound (q := q) hKb hL
    calc I2 ≤ C1 * (((1 + L / 2) ^ (-3 * q) * Real.exp (γ * L) + Real.exp (γ * L / 2)) / γ) := hb2
      _ ≤ C1 * (((2 ^ (3 * q) * (1 + L) ^ (-3 * q)) * Real.exp (γ * L) +
            Kb * (1 + L) ^ (-3 * q) * Real.exp (γ * L)) / γ) := by
          apply mul_le_mul_of_nonneg_left _ hC1
          apply div_le_div_of_nonneg_right _ hγ0.le
          exact add_le_add (mul_le_mul_of_nonneg_right hh1 (Real.exp_pos _).le) hh2
      _ = KB * (1 + L) ^ (-3 * q) * Real.exp (γ * L) := by rw [hKB]; field_simp
  have h2q : (0 : ℝ) ≤ 2 ^ q := by positivity
  calc 2 ^ q * ((F * Real.exp (dr * L)) ^ (q - 1) * I1 ^ q + I2)
      ≤ 2 ^ q * (KA * (1 + L) ^ (-3 * q) * Real.exp (γ * L) +
          KB * (1 + L) ^ (-3 * q) * Real.exp (γ * L)) :=
        mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) h2q
    _ = 2 ^ q * (KA + KB) * (1 + L) ^ (-3 * q) * Real.exp (γ * L) := by ring

end CoarseDeGiorgi.SharpnessExamples
