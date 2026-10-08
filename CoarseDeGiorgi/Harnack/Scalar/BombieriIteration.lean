import CoarseDeGiorgi.Harnack.Scalar.BombieriLemmas
import Mathlib.Analysis.SpecificLimits.Basic

namespace CoarseDeGiorgi.Harnack.Scalar

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

/-- The radii `ρ_j = 7/8 - (1/8) q^j`, `q = exp (-log 2 / (12 ξ))`, of the iteration in
`l.bombieri`. -/
def bombieriRadius (ξ : ℝ) (j : ℕ) : ℝ :=
  7 / 8 - 1 / 8 * (Real.exp (-(Real.log 2) / (12 * ξ))) ^ j

/-- The ratio `q = exp (-log 2 / (12 ξ))` of the radii `bombieriRadius`. -/
def bombieriRadiusRatio (ξ : ℝ) : ℝ := Real.exp (-(Real.log 2) / (12 * ξ))

/-- The ratio `2 ^ (-1/2)` of the geometric series in the iteration over radii. -/
def bombieriSeriesRatio : ℝ := Real.exp (-(Real.log 2) / 2)

/-- The radii `bombieriRadius ξ j` lie in `[3/4, 7/8]`. -/
theorem bombieri_radius_bounds {ξ : ℝ} (hξ : 0 < ξ) (j : ℕ) :
    3 / 4 ≤ bombieriRadius ξ j ∧ bombieriRadius ξ j ≤ 7 / 8 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 12 * ξ := by positivity
  have hexp_arg : -(Real.log 2) / (12 * ξ) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hlog) hden
  have hq0 : 0 < bombieriRadiusRatio ξ := Real.exp_pos _
  have hq1 : bombieriRadiusRatio ξ < 1 :=
    (Real.exp_lt_one_iff).2 hexp_arg
  have hqle : bombieriRadiusRatio ξ ≤ 1 := hq1.le
  have hp0 : 0 < (bombieriRadiusRatio ξ) ^ j := pow_pos hq0 _
  have hple : (bombieriRadiusRatio ξ) ^ j ≤ 1 := pow_le_one₀ hq0.le hqle
  have hp0' : 0 < (Real.exp (-(Real.log 2) / (12 * ξ))) ^ j := by
    simpa [bombieriRadiusRatio] using hp0
  have hple' : (Real.exp (-(Real.log 2) / (12 * ξ))) ^ j ≤ 1 := by
    simpa [bombieriRadiusRatio] using hple
  constructor
  · dsimp [bombieriRadius]
    nlinarith [hple']
  · dsimp [bombieriRadius]
    nlinarith [hp0']

/-- The gap between consecutive radii `bombieriRadius ξ j` is `(1/8) (1 - q) q^j`. -/
theorem bombieri_radius_step {ξ : ℝ} (j : ℕ) :
    bombieriRadius ξ (j + 1) - bombieriRadius ξ j =
      (1 / 8) * (1 - bombieriRadiusRatio ξ) *
        (bombieriRadiusRatio ξ) ^ j := by
  simp only [bombieriRadius, bombieriRadiusRatio, pow_succ]
  ring

/-- Consecutive radii `bombieriRadius ξ j` are strictly increasing. -/
theorem bombieri_radius_gap_pos {ξ : ℝ} (hξ : 0 < ξ) (j : ℕ) :
    0 < bombieriRadius ξ (j + 1) - bombieriRadius ξ j := by
  rw [bombieri_radius_step]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 12 * ξ := by positivity
  have harg : -(Real.log 2) / (12 * ξ) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hlog) hden
  have hq : bombieriRadiusRatio ξ < 1 := (Real.exp_lt_one_iff).2 harg
  have hp : 0 < (bombieriRadiusRatio ξ) ^ j := pow_pos (Real.exp_pos _) _
  positivity

/-- The gap power `(ρ_{j+1} - ρ_j) ^ (-6 ξ)` equals `(8 / (1 - q)) ^ (6 ξ) 2 ^ (j / 2)`. -/
theorem bombieri_radius_gap_rpow {ξ : ℝ} (hξ : 0 < ξ) (j : ℕ) :
    (bombieriRadius ξ (j + 1) - bombieriRadius ξ j) ^ (-6 * ξ) =
      (8 / (1 - bombieriRadiusRatio ξ)) ^ (6 * ξ) *
        2 ^ ((j : ℝ) / 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 12 * ξ := by positivity
  have harg : -(Real.log 2) / (12 * ξ) < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hlog) hden
  have hqpos : 0 < bombieriRadiusRatio ξ := Real.exp_pos _
  have hq_lt : bombieriRadiusRatio ξ < 1 := (Real.exp_lt_one_iff).2 harg
  have hc : 0 < (1 / 8) * (1 - bombieriRadiusRatio ξ) := by positivity
  have hqpow : 0 < (bombieriRadiusRatio ξ) ^ j := pow_pos hqpos _
  have hgap := bombieri_radius_step (ξ := ξ) j
  have hinv : ((1 / 8) * (1 - bombieriRadiusRatio ξ))⁻¹ =
      8 / (1 - bombieriRadiusRatio ξ) := by
    field_simp
  have hqpowid : (bombieriRadiusRatio ξ) ^ j =
      Real.exp (-(Real.log 2) / (12 * ξ) * (j : ℝ)) := by
    dsimp [bombieriRadiusRatio]
    rw [← Real.rpow_natCast, ← Real.exp_mul]
  have hdecay : ((bombieriRadiusRatio ξ) ^ j) ^ (-6 * ξ) = 2 ^ ((j : ℝ) / 2) := by
    rw [hqpowid, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp
    ring
  rw [hgap, Real.mul_rpow hc.le hqpow.le, hdecay]
  have hneg : -6 * ξ = -(6 * ξ) := by ring
  rw [hneg, Real.rpow_neg_eq_inv_rpow, hinv]

/-- `bombieriSeriesRatio = 2 ^ (-1/2)`. -/
theorem bombieri_series_ratio_eq_rpow :
    bombieriSeriesRatio = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [bombieriSeriesRatio, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- `0 < bombieriSeriesRatio < 1`. -/
theorem bombieri_series_ratio_bounds :
    0 < bombieriSeriesRatio ∧ bombieriSeriesRatio < 1 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : -(Real.log 2) / 2 < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hlog) (by norm_num)
  constructor
  · exact Real.exp_pos _
  · exact (Real.exp_lt_one_iff).2 harg

/-- `(1/2) ^ j 2 ^ (j / 2) = bombieriSeriesRatio ^ j`. -/
theorem bombieri_radius_weight_identity (j : ℕ) :
    (1 / 2 : ℝ) ^ j * 2 ^ ((j : ℝ) / 2) = bombieriSeriesRatio ^ j := by
  have hpowNat (a : ℝ) : ((2 : ℝ) ^ a) ^ j = 2 ^ (a * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one]
    norm_num
  rw [hhalf, hpowNat (-1)]
  have hdiv : (j : ℝ) / 2 = (1 / 2 : ℝ) * (j : ℝ) := by ring
  rw [hdiv, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [show (-1 : ℝ) * (j : ℝ) + (1 / 2 : ℝ) * (j : ℝ) =
      (-(1 / 2 : ℝ)) * (j : ℝ) by ring]
  rw [← hpowNat (-(1 / 2 : ℝ)), ← bombieri_series_ratio_eq_rpow]

/-- The partial sums of the geometric series with ratio `bombieriSeriesRatio` are at most its
sum. -/
theorem bombieri_series_sum_bound (n : ℕ) :
    (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) ≤
      1 / (1 - bombieriSeriesRatio) := by
  obtain ⟨hr0, hr1⟩ := bombieri_series_ratio_bounds
  have hne : bombieriSeriesRatio ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq hne]
  have hden : 0 < 1 - bombieriSeriesRatio := by linarith
  have hpow : 0 ≤ bombieriSeriesRatio ^ n := pow_nonneg hr0.le _
  have hsum : (bombieriSeriesRatio ^ n - 1) / (bombieriSeriesRatio - 1) =
      (1 - bombieriSeriesRatio ^ n) / (1 - bombieriSeriesRatio) := by
    field_simp [hne]
    ring
  rw [hsum]
  apply (div_le_div_iff_of_pos_right hden).2
  nlinarith

/-- Iteration over radii in `l.bombieri`: a bounded `f` with `f ρ ≤ f R / 2 + K (R - ρ) ^ (-6 ξ)`
satisfies `f (3/4) ≤ K (8 / (1 - q)) ^ (6 ξ) (1 - 2 ^ (-1/2))⁻¹`. -/
theorem bombieri_radius_iteration {ξ K M : ℝ} (hξ : 0 < ξ) (hK : 0 ≤ K)
    {f : ℝ → ℝ}
    (hbound : ∀ r, 3 / 4 ≤ r → r ≤ 7 / 8 → f r ≤ M)
    (hstep : ∀ ρ R, 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      f ρ ≤ f R / 2 + K * (R - ρ) ^ (-6 * ξ)) :
    f (3 / 4) ≤ K * (8 / (1 - bombieriRadiusRatio ξ)) ^ (6 * ξ) *
      (1 - bombieriSeriesRatio)⁻¹ := by
  let r : ℕ → ℝ := bombieriRadius ξ
  let S : ℝ := K * (8 / (1 - bombieriRadiusRatio ξ)) ^ (6 * ξ)
  have hS : 0 ≤ S := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have harg : -(Real.log 2) / (12 * ξ) < 0 :=
      div_neg_of_neg_of_pos (neg_neg_of_pos hlog) (by positivity)
    have hq : bombieriRadiusRatio ξ < 1 := (Real.exp_lt_one_iff).2 harg
    have hden : 0 < 1 - bombieriRadiusRatio ξ := by linarith
    have hfactor : 0 ≤ (8 / (1 - bombieriRadiusRatio ξ)) ^ (6 * ξ) := by
      positivity
    exact mul_nonneg hK hfactor
  have hrrec (j : ℕ) : f (r j) ≤ f (r (j + 1)) / 2 +
      S * 2 ^ ((j : ℝ) / 2) := by
    have hb := bombieri_radius_bounds hξ j
    have hb' := bombieri_radius_bounds hξ (j + 1)
    have hlt : r j < r (j + 1) := by
      exact sub_pos.mp (bombieri_radius_gap_pos hξ j)
    have hs := hstep (r j) (r (j + 1)) hb.1 hlt hb'.2
    dsimp [S, r]
    calc
      f (bombieriRadius ξ j) ≤ f (bombieriRadius ξ (j + 1)) / 2 +
          K * ((bombieriRadius ξ (j + 1) - bombieriRadius ξ j) ^ (-6 * ξ)) := hs
      _ = f (bombieriRadius ξ (j + 1)) / 2 +
          (K * (8 / (1 - bombieriRadiusRatio ξ)) ^ (6 * ξ)) *
            2 ^ ((j : ℝ) / 2) := by
        rw [bombieri_radius_gap_rpow hξ j]
        ring
  have hiter : ∀ n : ℕ, f (r 0) ≤
      (1 / 2 : ℝ) ^ n * f (r n) + S *
        (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hmult := mul_le_mul_of_nonneg_left (hrrec n)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)
      calc
        f (r 0) ≤ (1 / 2 : ℝ) ^ n * f (r n) +
            S * (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) := ih
        _ ≤ (1 / 2 : ℝ) ^ n *
              (f (r (n + 1)) / 2 + S * 2 ^ ((n : ℝ) / 2)) +
            S * (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) := by
          exact add_le_add hmult le_rfl
        _ = (1 / 2 : ℝ) ^ (n + 1) * f (r (n + 1)) +
            S * (∑ j ∈ Finset.range (n + 1), bombieriSeriesRatio ^ j) := by
          rw [Finset.sum_range_succ]
          calc
            (1 / 2 : ℝ) ^ n *
                (f (r (n + 1)) / 2 + S * 2 ^ ((n : ℝ) / 2)) +
                S * (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) =
              (1 / 2 : ℝ) ^ (n + 1) * f (r (n + 1)) +
                S * ((1 / 2 : ℝ) ^ n * 2 ^ ((n : ℝ) / 2)) +
                S * (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) := by ring
            _ = (1 / 2 : ℝ) ^ (n + 1) * f (r (n + 1)) +
                S * bombieriSeriesRatio ^ n +
                S * (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) := by
              rw [bombieri_radius_weight_identity]
            _ = (1 / 2 : ℝ) ^ (n + 1) * f (r (n + 1)) +
                S * ((∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) +
                  bombieriSeriesRatio ^ n) := by ring
  have hpartial (n : ℕ) : f (r 0) ≤
      (1 / 2 : ℝ) ^ n * M + S * (1 / (1 - bombieriSeriesRatio)) := by
    have hb := bombieri_radius_bounds hξ n
    have hiterN := hiter n
    have hsum := bombieri_series_sum_bound n
    calc
      f (r 0) ≤ (1 / 2 : ℝ) ^ n * f (r n) +
          S * (∑ j ∈ Finset.range n, bombieriSeriesRatio ^ j) := hiterN
      _ ≤ (1 / 2 : ℝ) ^ n * M + S * (1 / (1 - bombieriSeriesRatio)) := by
        gcongr
        · exact hbound (r n) hb.1 hb.2
  have hhalf : 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by norm_num
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hhalf.1 hhalf.2).const_mul M
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * M +
      S * (1 / (1 - bombieriSeriesRatio))) atTop
      (𝓝 (S * (1 / (1 - bombieriSeriesRatio)))) := by
    simpa [mul_comm] using ht.add tendsto_const_nhds
  have hout := ge_of_tendsto' hlim (fun n => hpartial n)
  have hr0 : r 0 = 3 / 4 := by
    dsimp [r, bombieriRadius]
    norm_num
  rw [hr0] at hout
  simpa [S] using hout

end

end CoarseDeGiorgi.Harnack.Scalar
