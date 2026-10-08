import CoarseDeGiorgi.Foundations.Iteration.Dyadic
import Mathlib.Analysis.SpecificLimits.Basic

namespace CoarseDeGiorgi.Foundations.Iteration

open Filter Finset
open scoped ENNReal Topology

noncomputable section

def holeFillingConstant (ε κ : ℝ) : ℝ :=
  (2 : ℝ) ^ κ / (1 - (2 * ε) * (2 : ℝ) ^ κ)

theorem holeFillingConstant_of_half {ε κ : ℝ}
    (hratio : (2 * ε) * (2 : ℝ) ^ κ = 1 / 2) :
    holeFillingConstant ε κ = 2 * (2 : ℝ) ^ κ := by
  rw [holeFillingConstant, hratio]
  norm_num
  ring

theorem ofReal_holeFillingConstant {ε κ : ℝ} (hε : 0 ≤ ε)
    (hsmall : (2 * ε) * (2 : ℝ) ^ κ < 1) :
    ENNReal.ofReal (holeFillingConstant ε κ) = ENNReal.ofReal ((2 : ℝ) ^ κ) *
      (1 - ENNReal.ofReal (2 * ε) * ENNReal.ofReal ((2 : ℝ) ^ κ))⁻¹ := by
  have hq : 0 ≤ 2 * ε := by linarith only [hε]
  have hg : 0 ≤ (2 : ℝ) ^ κ := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) κ).le
  rw [holeFillingConstant, ENNReal.ofReal_div_of_pos (sub_pos.mpr hsmall),
    ENNReal.ofReal_sub _ (mul_nonneg hq hg), ENNReal.ofReal_one,
    ENNReal.ofReal_mul hq, div_eq_mul_inv]

theorem ennreal_iteration_finite {y : ℕ → ℝ≥0∞} {q g a T : ℝ≥0∞}
    (hstep : ∀ n, y n ≤ q * y (n + 1) + a * g ^ (n + 1))
    (hbound : ∀ n, y n ≤ T) (N : ℕ) :
    y 0 ≤ q ^ N * T + a * ∑ i ∈ range N, q ^ i * g ^ (i + 1) := by
  have h : ∀ N, y 0 ≤ q ^ N * y N + a * ∑ i ∈ range N, q ^ i * g ^ (i + 1) := by
    intro N
    induction N with
    | zero => simp only [pow_zero, one_mul, sum_range_zero, mul_zero, add_zero, le_refl]
    | succ N ih =>
      calc
        y 0 ≤ q ^ N * y N + a * ∑ i ∈ range N, q ^ i * g ^ (i + 1) := ih
        _ ≤ q ^ N * (q * y (N + 1) + a * g ^ (N + 1)) +
            a * ∑ i ∈ range N, q ^ i * g ^ (i + 1) :=
          add_le_add (mul_le_mul' le_rfl (hstep N)) le_rfl
        _ = q ^ (N + 1) * y (N + 1) + a * ∑ i ∈ range (N + 1), q ^ i * g ^ (i + 1) := by
          simp only [sum_range_succ, mul_add, pow_succ]
          ac_rfl
  exact (h N).trans (add_le_add (mul_le_mul' le_rfl (hbound N)) le_rfl)

theorem ennreal_iteration_limit {y : ℕ → ℝ≥0∞} {q g a T : ℝ≥0∞}
    (hstep : ∀ n, y n ≤ q * y (n + 1) + a * g ^ (n + 1))
    (hbound : ∀ n, y n ≤ T) (hT : T < ⊤) (hq : q < 1) :
    y 0 ≤ a * g * (1 - q * g)⁻¹ := by
  have hs : ∀ N, (∑ i ∈ range N, q ^ i * g ^ (i + 1)) ≤ g * (1 - q * g)⁻¹ := by
    intro N
    calc
      (∑ i ∈ range N, q ^ i * g ^ (i + 1)) ≤ ∑' i : ℕ, q ^ i * g ^ (i + 1) :=
        ENNReal.sum_le_tsum _
      _ = g * (1 - q * g)⁻¹ := by
        simp_rw [pow_succ, show ∀ i : ℕ, q ^ i * (g ^ i * g) = g * (q * g) ^ i
          from fun i => by rw [mul_pow]; ac_rfl]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hb : ∀ N, y 0 ≤ q ^ N * T + a * g * (1 - q * g)⁻¹ := fun N =>
    (ennreal_iteration_finite hstep hbound N).trans
      (add_le_add le_rfl ((mul_le_mul' (le_refl a) (hs N)).trans_eq (mul_assoc _ _ _).symm))
  have ht := ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) (Or.inr (ne_of_lt hT))
  have hlim : Tendsto (fun N : ℕ => q ^ N * T + a * g * (1 - q * g)⁻¹) atTop
      (𝓝 (a * g * (1 - q * g)⁻¹)) := by
    simpa only [zero_mul, zero_add] using ht.add_const (a * g * (1 - q * g)⁻¹)
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hb

/-- Hole filling needs the estimate only between consecutive increasing dyadic radii. -/
theorem hole_filling {f : ℝ → ℝ≥0∞} (hf : Monotone f)
    {ρ R ε A κ : ℝ} (hρR : ρ < R) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hsmall : (2 * ε) * (2 : ℝ) ^ κ < 1) (hfinite : f R < ⊤)
    (hstep : ∀ i : ℕ, f (holeRadius ρ R i) ≤ ENNReal.ofReal (2 * ε) *
      f (holeRadius ρ R (i + 1)) + ENNReal.ofReal
        (A * (holeRadius ρ R (i + 1) - holeRadius ρ R i) ^ (-κ))) :
    f ρ ≤ ENNReal.ofReal (holeFillingConstant ε κ) *
      ENNReal.ofReal A * ENNReal.ofReal ((R - ρ) ^ (-κ)) := by
  have hq : ENNReal.ofReal (2 * ε) < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    have hg := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hκ
    have hmul := mul_le_mul_of_nonneg_left hg (by linarith only [hε] : 0 ≤ 2 * ε)
    linarith only [hsmall, hmul]
  have hs : ∀ i, f (holeRadius ρ R i) ≤ ENNReal.ofReal (2 * ε) *
      f (holeRadius ρ R (i + 1)) +
        (ENNReal.ofReal A * ENNReal.ofReal ((R - ρ) ^ (-κ))) *
          (ENNReal.ofReal ((2 : ℝ) ^ κ)) ^ (i + 1) := by
    intro i
    have hi := hstep i
    rw [holeRadius_gap, dyadicGap_rpow_full (sub_pos.mpr hρR), ENNReal.ofReal_mul hA,
      ENNReal.ofReal_mul (pow_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) κ).le _),
      ENNReal.ofReal_pow (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) κ).le] at hi
    convert hi using 1; ac_rfl
  have h := ennreal_iteration_limit hs
    (fun i => hf (holeRadius_bounds hρR i).2.le) hfinite hq
  rw [holeRadius_zero] at h
  rw [ofReal_holeFillingConstant hε hsmall]
  convert h using 1; ac_rfl

theorem hole_filling_of_all_pairs {f : ℝ → ℝ≥0∞} (hf : Monotone f)
    {ρ R ε A κ : ℝ} (hρR : ρ < R) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hκ : 0 ≤ κ)
    (hsmall : (2 * ε) * (2 : ℝ) ^ κ < 1) (hfinite : f R < ⊤)
    (hstep : ∀ ρ' R' : ℝ, ρ ≤ ρ' → ρ' < R' → R' ≤ R →
      f ρ' ≤ ENNReal.ofReal (2 * ε) * f R' + ENNReal.ofReal (A * (R' - ρ') ^ (-κ))) :
    f ρ ≤ ENNReal.ofReal (holeFillingConstant ε κ) *
      ENNReal.ofReal A * ENNReal.ofReal ((R - ρ) ^ (-κ)) := by
  apply hole_filling hf hρR hε hA hκ hsmall hfinite
  intro i
  apply hstep _ _ (holeRadius_bounds hρR i).1 _ (holeRadius_bounds hρR (i + 1)).2.le
  exact sub_pos.mp (by rw [holeRadius_gap]; exact dyadicGap_pos (sub_pos.mpr hρR) i)

end

end CoarseDeGiorgi.Foundations.Iteration
