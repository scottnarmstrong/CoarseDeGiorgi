module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessMeans

/-! # The blow-up of the `L^η` means: explicit power bounds -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem whLog_cube_le {d : ℕ} (hd : 1 ≤ d) {θ ε : ℝ} (hθ : 0 < θ) (hε : 0 < ε)
    (h2ε : 2 * ε ≤ whR d) :
    whLog d (2 * ε) ^ 3 ≤ (Real.exp 1 * whR d / (2 * ε)) ^ θ / (θ / 3) ^ 3 := by
  have hρ : 0 < 2 * ε := by positivity
  have hx : 0 < Real.exp 1 * whR d / (2 * ε) :=
    div_pos (mul_pos (Real.exp_pos 1) (whR_pos hd)) hρ
  have h1 := Real.log_le_rpow_div hx.le (show 0 < θ / 3 by positivity)
  rw [← whLog_eq hd hρ] at h1
  have h0 : 0 ≤ whLog d (2 * ε) := by linarith [one_le_whLog hρ h2ε]
  have h3 : whLog d (2 * ε) ^ 3 ≤ ((Real.exp 1 * whR d / (2 * ε)) ^ (θ / 3) / (θ / 3)) ^ 3 :=
    pow_le_pow_left₀ h0 h1 3
  refine h3.trans (le_of_eq ?_)
  rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 3
  push_cast; ring

theorem rpow_two_pow_eps {ε : ℝ} (hε : 0 < ε) (z : ℝ) : (8 * ε ^ 2) ^ z = 8 ^ z * ε ^ (2 * z) := by
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  push_cast
  ring_nf

theorem sqrt_eight_mul_rpow {ε : ℝ} (hε : 0 < ε) (β : ℝ) :
    (Real.sqrt 8 * ε) ^ β = 8 ^ (β / 2) * ε ^ β := by
  rw [Real.mul_rpow (Real.sqrt_nonneg _) hε.le, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
  congr 2
  ring

theorem div_two_eps_rpow {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) (θ : ℝ) :
    (c / (2 * ε)) ^ θ = (c / 2) ^ θ * ε ^ (-θ) := by
  rw [show c / (2 * ε) = c / 2 * ε⁻¹ by field_simp, Real.mul_rpow (by positivity)
    (inv_nonneg.2 hε.le), Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]

/-- The pole value of `U_ε` is at least a constant times a power of `ε`. -/
theorem whG_lower {d : ℕ} (hd : 3 ≤ d) {q t : ℝ} {θ : ℝ} (hθ : 0 < θ) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      C0 * ε ^ (2 - (d : ℝ) - whBeta d q t + θ) ≤
        4 * ε ^ 2 * ((8 * ε ^ 2) ^ (-((d : ℝ) / 2)) /
          (2 * ((Real.sqrt 8 * ε) ^ whBeta d q t * whLog d (2 * ε) ^ 3))) := by
  have hd1 : 1 ≤ d := by omega
  have hR := whR_pos hd1
  have hR1 : (1 : ℝ) ≤ whR d := by
    unfold whR; rw [Real.one_le_sqrt]; exact_mod_cast hd1
  set β := whBeta d q t with hβdef
  set D : ℝ := (d : ℝ) with hD
  set c0 : ℝ := Real.exp 1 * whR d with hc0
  have hc0pos : 0 < c0 := mul_pos (Real.exp_pos 1) hR
  refine ⟨4 * (8 ^ (-(D / 2)) * (θ / 3) ^ 3 / (2 * (8 ^ (β / 2) * (c0 / 2) ^ θ))), by positivity,
    fun ε hε hε8 => ?_⟩
  have h2ε : 2 * ε ≤ whR d := by linarith
  have hlog := whLog_cube_le hd1 hθ hε h2ε
  rw [← hc0] at hlog
  have hℓ1 := one_le_whLog (d := d) (by positivity : 0 < 2 * ε) h2ε
  have hAp : 0 < (c0 / (2 * ε)) ^ θ / (θ / 3) ^ 3 := by positivity
  have hKc : (8 * ε ^ 2) ^ (-(D / 2)) / (2 * ((Real.sqrt 8 * ε) ^ β * ((c0 / (2 * ε)) ^ θ / (θ / 3) ^ 3))) ≤
      (8 * ε ^ 2) ^ (-(D / 2)) / (2 * ((Real.sqrt 8 * ε) ^ β * whLog d (2 * ε) ^ 3)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : 0 ≤ 2 := by norm_num
    have h3 : (Real.sqrt 8 * ε) ^ β * whLog d (2 * ε) ^ 3 ≤
        (Real.sqrt 8 * ε) ^ β * ((c0 / (2 * ε)) ^ θ / (θ / 3) ^ 3) :=
      mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg (by positivity) _)
    linarith
  have hexpr : (8 * ε ^ 2) ^ (-(D / 2)) /
      (2 * ((Real.sqrt 8 * ε) ^ β * ((c0 / (2 * ε)) ^ θ / (θ / 3) ^ 3))) =
      (8 ^ (-(D / 2)) * (θ / 3) ^ 3 / (2 * (8 ^ (β / 2) * (c0 / 2) ^ θ))) *
        ε ^ (-D - β + θ) := by
    rw [rpow_two_pow_eps hε, sqrt_eight_mul_rpow hε, div_two_eps_rpow hε hc0pos.le]
    have e1 : ε ^ (-D - β + θ) = ε ^ (2 * (-(D / 2))) / (ε ^ β * ε ^ (-θ)) := by
      rw [← Real.rpow_add hε, ← Real.rpow_sub hε]
      congr 1; ring
    rw [e1]
    have : (0 : ℝ) < ε ^ β := Real.rpow_pos_of_pos hε _
    have : (0 : ℝ) < ε ^ (-θ) := Real.rpow_pos_of_pos hε _
    field_simp
  have hεp : ε ^ 2 * ε ^ (-D - β + θ) = ε ^ (2 - D - β + θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hε]
    congr 1; push_cast; ring
  calc 4 * (8 ^ (-(D / 2)) * (θ / 3) ^ 3 / (2 * (8 ^ (β / 2) * (c0 / 2) ^ θ))) *
        ε ^ (2 - D - β + θ)
      = 4 * ε ^ 2 * ((8 ^ (-(D / 2)) * (θ / 3) ^ 3 / (2 * (8 ^ (β / 2) * (c0 / 2) ^ θ))) *
          ε ^ (-D - β + θ)) := by rw [← hεp]; ring
    _ = 4 * ε ^ 2 * ((8 * ε ^ 2) ^ (-(D / 2)) /
          (2 * ((Real.sqrt 8 * ε) ^ β * ((c0 / (2 * ε)) ^ θ / (θ / 3) ^ 3)))) := by rw [hexpr]
    _ ≤ _ := mul_le_mul_of_nonneg_left hKc (by positivity)

theorem Z_lower_of_G {d : ℕ} (hd : 1 ≤ d) {η p C0 : ℝ} (hη : 0 < η) (hC0 : 0 < C0)
    (hp : p * η + d < 0) {G : ℝ → ℝ}
    (hG : ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → C0 * ε ^ p ≤ G ε) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      C * ε ^ (-s) ≤ ((((5 / 8 : ℝ) ^ d)⁻¹ * G ε ^ η * (4 * ε / whR d) ^ d) ^ (1 / η)) := by
  have hR := whR_pos hd
  set C1 : ℝ := ((5 / 8 : ℝ) ^ d)⁻¹ * C0 ^ η * (4 / whR d) ^ d with hC1
  have hC1pos : 0 < C1 := by positivity
  refine ⟨-(p * η + d) / η, C1 ^ (1 / η), by
    have : 0 < -(p * η + d) := by linarith
    positivity, by positivity, fun ε hε hε8 => ?_⟩
  have hGp : C0 * ε ^ p ≤ G ε := hG ε hε hε8
  have hY : C1 * ε ^ (p * η + d) ≤ ((5 / 8 : ℝ) ^ d)⁻¹ * G ε ^ η * (4 * ε / whR d) ^ d := by
    have h1 : (C0 * ε ^ p) ^ η ≤ G ε ^ η :=
      Real.rpow_le_rpow (by positivity) hGp hη.le
    have h2 : (C0 * ε ^ p) ^ η = C0 ^ η * ε ^ (p * η) := by
      rw [Real.mul_rpow hC0.le (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
    have h3 : (4 * ε / whR d) ^ d = (4 / whR d) ^ d * ε ^ (d : ℝ) := by
      rw [show 4 * ε / whR d = 4 / whR d * ε by ring, mul_pow, Real.rpow_natCast]
    have h4 : C1 * ε ^ (p * η + d) = ((5 / 8 : ℝ) ^ d)⁻¹ * (C0 ^ η * ε ^ (p * η)) *
        ((4 / whR d) ^ d * ε ^ (d : ℝ)) := by
      rw [hC1, Real.rpow_add hε]
      ring
    rw [h4, h3]
    rw [← h2]
    have hpos : 0 ≤ ((5 / 8 : ℝ) ^ d)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hpos) (by positivity)
  have hr : (0 : ℝ) ≤ 1 / η := by positivity
  calc C1 ^ (1 / η) * ε ^ (-(-(p * η + d) / η))
      = (C1 * ε ^ (p * η + d)) ^ (1 / η) := by
        rw [Real.mul_rpow hC1pos.le (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le]
        congr 2
        field_simp
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hY hr

end

end CoarseDeGiorgi.SharpnessExamples
