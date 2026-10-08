module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessInfimum
public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessAnalysis

/-! # A lower bound for the value of the supersolution at the pole -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Lower bound for `K` on `[4ε², 8ε²]`. -/
theorem whK_lower {d : ℕ} (hd : 1 ≤ d) {q t : ℝ} (hβ : 0 < whBeta d q t) {ε σ : ℝ} (hε : 0 < ε)
    (hε8 : ε < 1 / 8) (hσ1 : 4 * ε ^ 2 ≤ σ) (hσ2 : σ ≤ 8 * ε ^ 2) :
    (8 * ε ^ 2) ^ (-((d : ℝ) / 2)) /
        (2 * ((Real.sqrt 8 * ε) ^ whBeta d q t * whLog d (2 * ε) ^ 3)) ≤ whK d q t σ := by
  have hσ0 : 0 < σ := by nlinarith [pow_pos hε 2]
  have hd3 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set β := whBeta d q t with hβdef
  have hR1 : (1 : ℝ) ≤ whR d := by
    unfold whR; rw [Real.one_le_sqrt]; exact hd3
  -- the radius bounds
  have h2e : 2 * ε ≤ Real.sqrt σ := by
    rw [show 2 * ε = Real.sqrt ((2 * ε) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsq : Real.sqrt σ ≤ Real.sqrt 8 * ε := by
    rw [show Real.sqrt 8 * ε = Real.sqrt (8 * ε ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hε.le]]
    exact Real.sqrt_le_sqrt hσ2
  have hρ0 : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ0
  have hρR : Real.sqrt σ ≤ whR d := by
    have : σ ≤ d := by nlinarith [pow_pos hε 2]
    unfold whR; exact Real.sqrt_le_sqrt this
  have hℓ1 := one_le_whLog (d := d) hρ0 hρR
  have hℓ : whLog d (Real.sqrt σ) ≤ whLog d (2 * ε) := whLog_anti (by positivity) h2e
  -- bound on whAs
  have hA : whAs d q t σ ≤ (Real.sqrt 8 * ε) ^ β * whLog d (2 * ε) ^ 3 := by
    unfold whAs whA
    apply mul_le_mul
    · exact Real.rpow_le_rpow hρ0.le hsq hβ.le
    · exact pow_le_pow_left₀ (by linarith) hℓ 3
    · exact pow_nonneg (by linarith) _
    · exact Real.rpow_nonneg (by positivity) _
  have hApos : 0 < whAs d q t σ := whAs_pos (d := d) (q := q) (t := t) hσ0 (by nlinarith [pow_pos hε 2])
  have hQ : (8 * ε ^ 2) ^ (-((d : ℝ) / 2)) ≤ whQ d σ := by
    unfold whQ
    exact Real.rpow_le_rpow_of_nonpos hσ0 hσ2 (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith)
  unfold whK
  apply div_le_div₀ (whQ_pos hσ0).le hQ (by positivity) (by linarith)

/-- The lower bound for `U_ε(4ε²)`. -/
theorem whU_lower {d : ℕ} (hd : 3 ≤ d) {q t : ℝ} (hβ : 0 < whBeta d q t) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε < 1 / 8) :
    4 * ε ^ 2 * ((8 * ε ^ 2) ^ (-((d : ℝ) / 2)) /
        (2 * ((Real.sqrt 8 * ε) ^ whBeta d q t * whLog d (2 * ε) ^ 3))) ≤
      whU d q t ε (4 * ε ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h8 : 8 * ε ^ 2 ≤ (d : ℝ) / 2 := by nlinarith
  have h48 : 4 * ε ^ 2 ≤ 8 * ε ^ 2 := by nlinarith [pow_pos hε 2]
  have hlt1 : 4 * ε ^ 2 < d := by nlinarith
  have hlt2 : 8 * ε ^ 2 < d := by nlinarith
  have hlt3 : (d : ℝ) / 2 < d := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (whk_intervalIntegrable q t hε hlt1 hlt2) (whk_intervalIntegrable q t hε hlt2 hlt3)
  have hsecond : 0 ≤ ∫ σ in (8 * ε ^ 2)..((d : ℝ) / 2), whk d q t ε σ :=
    intervalIntegral.integral_nonneg h8 (fun u hu => whk_nonneg q t (by linarith [hu.2]))
  set Kc := (8 * ε ^ 2) ^ (-((d : ℝ) / 2)) /
        (2 * ((Real.sqrt 8 * ε) ^ whBeta d q t * whLog d (2 * ε) ^ 3)) with hKc
  have hfirst : (8 * ε ^ 2 - 4 * ε ^ 2) * Kc ≤ ∫ σ in (4 * ε ^ 2)..(8 * ε ^ 2), whk d q t ε σ := by
    rw [← smul_eq_mul, ← intervalIntegral.integral_const]
    apply intervalIntegral.integral_mono_on h48 intervalIntegrable_const
      (whk_intervalIntegrable q t hε hlt1 hlt2)
    intro σ hσ
    have := whK_lower hd1 hβ hε hε8 hσ.1 hσ.2
    unfold whk
    rw [whP_eq_one hε hσ.1, one_mul]
    exact this
  unfold whU
  have : 8 * ε ^ 2 - 4 * ε ^ 2 = 4 * ε ^ 2 := by ring
  rw [this] at hfirst
  linarith

end

end CoarseDeGiorgi.SharpnessExamples
