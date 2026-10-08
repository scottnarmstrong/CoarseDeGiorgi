module

public import CoarseDeGiorgi.Statements.BesovCubeNorm
public import CoarseDeGiorgi.Statements.CubeCell
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! The geometric-series step of `l.negative.sobolev`, including infinite negative norms. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- The Gaussian test factor at triadic time has the required growth exponent. -/
theorem lemmaB2_triadic_scale (β : ℝ) (k : ℕ) :
    Real.rpow ((3 : ℝ) ^ (-(2 * (k : ℤ)))) (-β / 2) = Real.rpow 3 ((k : ℝ) * β) := by
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- The loss of `ε` leaves a summable geometric weight. -/
theorem lemmaB2_geometric_sum (ε : ℝ) (hε : 0 < ε) :
    (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * ε / 2)))) =
      ENNReal.ofReal ((1 - Real.rpow 3 (-ε / 2))⁻¹) := by
  let r : ℝ := Real.rpow 3 (-ε / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hw (k : ℕ) : Real.rpow 3 (-((k : ℝ) * ε / 2)) = r ^ k := by
    rw [show -((k : ℝ) * ε / 2) = (-ε / 2) * (k : ℝ) by ring]
    exact Real.rpow_mul_natCast (by norm_num) _ _
  simp_rw [hw]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hr0 k)
    (summable_geometric_of_lt_one hr0 hr1), tsum_geometric_of_lt_one hr0 hr1]

/-- Cancellation of the heat-growth exponent against the Besov weight. -/
theorem lemmaB2_weight_identity (s ε : ℝ) (k : ℕ) :
    ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
      (ENNReal.ofReal (Real.rpow 3 ((k : ℝ) * (2 * s - ε)))).rpow (1 / 2) =
    ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * ε / 2))) := by
  simp only [ENNReal.rpow_eq_pow, Real.rpow_eq_pow]
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (by norm_num) _) (by norm_num),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 2
  ring

/-- Summing the square roots of the heat bounds. No finiteness assumption on `N` is needed. -/
theorem lemmaB2_heat_sum_le (s ε : ℝ) (hε : 0 < ε) (heat : ℕ → ℝ≥0∞)
    (A N : ℝ≥0∞)
    (hh : ∀ k : ℕ, heat k ≤ A * ENNReal.ofReal (Real.rpow 3 ((k : ℝ) * (2 * s - ε))) * N) :
    (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (heat k).rpow (1 / 2)) ≤
      ENNReal.ofReal ((1 - Real.rpow 3 (-ε / 2))⁻¹) * A.rpow (1 / 2) * N.rpow (1 / 2) := by
  simp only [ENNReal.rpow_eq_pow] at *
  calc
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (A * ENNReal.ofReal (Real.rpow 3 ((k : ℝ) * (2 * s - ε))) * N) ^ (1 / 2 : ℝ) := by
      exact ENNReal.tsum_le_tsum (fun k =>
        mul_le_mul_right (ENNReal.rpow_le_rpow (hh k) (by norm_num)) _)
    _ = (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * ε / 2)))) *
        (A ^ (1 / 2 : ℝ)) * (N ^ (1 / 2 : ℝ)) := by
      calc
        _ = ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * ε / 2))) *
            (A ^ (1 / 2 : ℝ)) * (N ^ (1 / 2 : ℝ)) := by
          apply tsum_congr
          intro k
          simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          have hid := lemmaB2_weight_identity s ε k
          simp only [ENNReal.rpow_eq_pow] at hid
          calc
            _ = (ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
                (ENNReal.ofReal (Real.rpow 3 ((k : ℝ) * (2 * s - ε))) ^ (1 / 2 : ℝ))) *
                (A ^ (1 / 2 : ℝ)) * (N ^ (1 / 2 : ℝ)) := by ac_rfl
            _ = _ := by rw [hid]
        _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    _ = _ := by rw [lemmaB2_geometric_sum ε hε]

/-- Squaring eliminates the square root even at zero and infinity. -/
theorem lemmaB2_square_root (N : ℝ≥0∞) : (N.rpow (1 / 2)) ^ 2 = N := by
  simp only [ENNReal.rpow_eq_pow]
  rw [← ENNReal.rpow_two (N ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul]
  norm_num

/-- The final square of the comparison and heat series has a linear factor `N`. -/
theorem lemmaB2_series_square_le (s ε : ℝ) (hε : 0 < ε) (heat : ℕ → ℝ≥0∞)
    (cubeSum B A N : ℝ≥0∞)
    (hcompare : cubeSum ≤ B.rpow (1 / 2) *
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * (heat k).rpow (1 / 2)))
    (hh : ∀ k : ℕ, heat k ≤ A * ENNReal.ofReal (Real.rpow 3 ((k : ℝ) * (2 * s - ε))) * N) :
    cubeSum ^ 2 ≤ B * ENNReal.ofReal ((1 - Real.rpow 3 (-ε / 2))⁻¹) ^ 2 * A * N := by
  have hsum := lemmaB2_heat_sum_le s ε hε heat A N hh
  have hb := hcompare.trans (mul_le_mul_right hsum (B.rpow (1 / 2)))
  calc
    _ ≤ (B.rpow (1 / 2) *
        (ENNReal.ofReal ((1 - Real.rpow 3 (-ε / 2))⁻¹) * A.rpow (1 / 2) * N.rpow (1 / 2))) ^ 2 :=
      pow_le_pow_left' hb 2
    _ = _ := by
      simp only [mul_pow, lemmaB2_square_root]
      ac_rfl

/-- The quasi-norm is the square of the cube series used in `p.besov.averages`. -/
theorem lemmaB2_besovCubeNorm_eq {d : ℕ} (b : Vec d → Mat d)
    (hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict (originCube 1)))
    (s p : ℝ) (hs : 0 < s) (hp : 1 ≤ p) :
    besovCubeNorm b hb s p hs hp =
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) *
        (ENNReal.ofReal
          ((∑ j : Fin d → Fin (3 ^ k), Real.rpow ‖volumeAverageMat (cubeCell k j) b‖ p) /
            ((Finset.univ : Finset (Fin d → Fin (3 ^ k))).card : ℝ))).rpow (1 / (2 * p))) ^ 2 := by
  rfl

end CoarseDeGiorgi.NegSobolev
