import CoarseDeGiorgi.Endpoint.Capacitary.Replacement
import CoarseDeGiorgi.Assembly.ClassicalMomentsSeries
import CoarseDeGiorgi.Weighted.LowerSpecNorm
import Mathlib.Analysis.MeanInequalitiesPow

/-! Uniform energy control of the remote capacity by the upper moment. -/

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The arithmetic mean of cell norms is bounded by the power mean. -/
theorem capacitary_cell_mean_bound (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {p : ℝ} (hp : 1 ≤ p) :
    ENNReal.ofReal (((triangulation (d := d) 4).attach.sum fun η =>
      ‖upperResponseOnCell 4 a ha η‖) / ((triangulation (d := d) 4).card : ℝ)) ≤
      (ENNReal.ofReal (upperCellAverage a ha 4 p)).rpow (1 / p) := by
  classical
  let T := triangulation (d := d) 4
  let N : ℝ := T.card
  let M : ℝ := (T.attach.sum fun η => ‖upperResponseOnCell 4 a ha η‖) / N
  have hN : 0 < N := Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d 4)
  have hM : 0 ≤ M := div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hN.le
  have hw : ∑ _η ∈ T.attach, N⁻¹ = (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_attach]
    exact mul_inv_cancel₀ hN.ne'
  have hj := Real.rpow_arith_mean_le_arith_mean_rpow T.attach
    (fun _ => N⁻¹) (fun η => ‖upperResponseOnCell 4 a ha η‖)
    (fun _ _ => inv_nonneg.mpr hN.le) hw (fun _ _ => norm_nonneg _) hp
  have hpow : M ^ p ≤ upperCellAverage a ha 4 p := by
    convert hj using 1
    · congr 1
      dsimp only [M]
      rw [← Finset.mul_sum, div_eq_mul_inv]
      ring
    · unfold upperCellAverage
      dsimp only [T, N]
      simp only [Real.rpow_eq_pow]
      rw [← Finset.mul_sum, div_eq_mul_inv]
      ring
  have hEN : (ENNReal.ofReal M).rpow p ≤ ENNReal.ofReal (upperCellAverage a ha 4 p) := by
    rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_nonneg hM (zero_le_one.trans hp)]
    exact ENNReal.ofReal_le_ofReal hpow
  have hr := ENNReal.rpow_le_rpow hEN (by positivity : 0 ≤ 1 / p)
  simp only [ENNReal.rpow_eq_pow] at hr
  rw [← ENNReal.rpow_mul, mul_one_div_cancel (zero_lt_one.trans_le hp).ne',
    ENNReal.rpow_one] at hr
  simpa only [ENNReal.rpow_eq_pow] using hr

/-- The weight of level four in the normalized half-power series. -/
noncomputable def capacitaryWeight (s : ℝ) : ℝ :=
  (1 - (3 : ℝ) ^ (-s)) * (3 : ℝ) ^ (-(4 * s))

theorem capacitaryWeight_pos {s : ℝ} (hs : 0 < s) : 0 < capacitaryWeight s := by
  apply mul_pos
  · exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs))
  · exact Real.rpow_pos_of_pos (by norm_num) _

/-- A single level is controlled by the upper moment. -/
theorem capacitary_level_bound (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    (ENNReal.ofReal (upperCellAverage a ha 4 p)).rpow (1 / p) ≤
      ENNReal.ofReal ((capacitaryWeight s)⁻¹ ^ 2) * upperMoment a ha s p hs hp := by
  let b : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal ((3 : ℝ) ^ (-((k : ℝ) * s))) *
    (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / (2 * p))
  have hsingle : ENNReal.ofReal (capacitaryWeight s) *
      (ENNReal.ofReal (upperCellAverage a ha 4 p)).rpow (1 / (2 * p)) ≤
      ENNReal.ofReal (1 - (3 : ℝ) ^ (-s)) * ∑' k, b k := by
    rw [capacitaryWeight, ENNReal.ofReal_mul (le_of_lt (sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)))), mul_assoc]
    exact mul_le_mul_right (by simpa only [b, Nat.cast_ofNat] using
      (ENNReal.le_tsum (f := b) 4)) _
  have hsq := pow_le_pow_left' hsingle 2
  rw [mul_pow, Assembly.ClassicalMomentsImpl.half_power_sq _ (zero_lt_one.trans_le hp)] at hsq
  change (ENNReal.ofReal (capacitaryWeight s)) ^ 2 * _ ≤ upperMoment a ha s p hs hp at hsq
  have hinv := mul_le_mul_right hsq (ENNReal.ofReal ((capacitaryWeight s)⁻¹ ^ 2))
  have hc : ENNReal.ofReal ((capacitaryWeight s)⁻¹ ^ 2) *
      ENNReal.ofReal (capacitaryWeight s) ^ 2 = 1 := by
    rw [← ENNReal.ofReal_pow (capacitaryWeight_pos hs).le,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [← mul_pow, inv_mul_cancel₀ (capacitaryWeight_pos hs).ne']
    norm_num
  rw [← mul_assoc, hc, one_mul] at hinv
  exact hinv

/-- Step 5: a zero-boundary competitor for the remote capacity has energy at most `C Λ`.
The constant is selected before the coefficient field. -/
theorem capacitary_competitor_energy [NeZero d] {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
      ∃ (f : Vec d → ℝ) (Gf : Vec d → Vec d), MemH1a0 a (originCube 1) f Gf ∧
        (∀ᵐ x ∂volume.restrict (originCube 1), x ∈ remoteCube d (1 / 2) → f x = 1) ∧
        weightedEnergy a (originCube 1) Gf ≤ ENNReal.ofReal C * upperMoment a ha s p hs hp := by
  classical
  let B : ℝ := (d : ℝ) * 81 ^ 2
  let W : ℝ := (capacitaryWeight s)⁻¹ ^ 2
  refine ⟨B * W, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (sq_nonneg _), ?_⟩
  intro a ha
  obtain ⟨f, Gf, hf, hfQ, hE⟩ := capacitary_replacement_exists a ha
  have hfmem := Weighted.MemH1a0.memH1a ha hf
  have hEf := (Weighted.MemH1a.energy_lt_top (originCube_domain one_pos).isOpen ha hfmem).ne
  let M : ℝ := ((triangulation (d := d) 4).attach.sum fun η =>
    ‖upperResponseOnCell 4 a ha η‖) / ((triangulation (d := d) 4).card : ℝ)
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hreal : (weightedEnergy a (originCube 1) Gf).toReal ≤ B * M := by
    rw [hE]
    have hcell (η : SimplexIndex d 4) :
        vecDot (capacitaryDirection η) (matVecMul (upperResponseOnCell 4 a ha η)
          (capacitaryDirection η)) ≤ ‖upperResponseOnCell 4 a ha η‖ * B :=
      (Weighted.LowerResponseImpl.lower_quadratic_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (capacitaryDirection_bound η) (norm_nonneg _))
    calc
      _ ≤ ((triangulation (d := d) 4).attach.sum fun η =>
          ‖upperResponseOnCell 4 a ha η‖ * B) /
          ((triangulation (d := d) 4).card : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum fun η _ => hcell η) (Nat.cast_nonneg _)
      _ = B * M := by rw [← Finset.sum_mul]; dsimp only [M]; ring
  refine ⟨f, Gf, hf, hfQ, ?_⟩
  calc
    _ = ENNReal.ofReal (weightedEnergy a (originCube 1) Gf).toReal :=
      (ENNReal.ofReal_toReal hEf).symm
    _ ≤ ENNReal.ofReal (B * M) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal B * ENNReal.ofReal M := ENNReal.ofReal_mul hB
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (upperCellAverage a ha 4 p)).rpow (1 / p) :=
      mul_le_mul_right (capacitary_cell_mean_bound a ha hp) _
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal W * upperMoment a ha s p hs hp) :=
      mul_le_mul_right (capacitary_level_bound a ha hs hp) _
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hB]

end CoarseDeGiorgi.Endpoint
