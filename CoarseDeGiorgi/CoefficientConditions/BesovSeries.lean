module

public import CoarseDeGiorgi.CoefficientConditions.BesovLevel
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.UpperMoment
public import CoarseDeGiorgi.Statements.LowerMoment

/-! # The series comparison for `moment_bounds_besov` -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.CoefficientConditions

/-- `(d!)^{1/2}` as a real number. -/
noncomputable def sqrtFact (d : ℕ) : ℝ := Real.rpow (d.factorial : ℝ) (1 / 2)

theorem sqrtFact_sq (d : ℕ) : sqrtFact d ^ 2 = (d.factorial : ℝ) := by
  unfold sqrtFact
  rw [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem sqrtFact_nonneg (d : ℕ) : 0 ≤ sqrtFact d := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem root_le {d : ℕ} {U C p : ℝ} (hp : 0 < p) (_hC : 0 ≤ C)
    (h : U ≤ Real.rpow (d.factorial : ℝ) p * C) :
    (ENNReal.ofReal U).rpow (1 / (2 * p)) ≤
      ENNReal.ofReal (sqrtFact d) * (ENNReal.ofReal C).rpow (1 / (2 * p)) := by
  have hr : 0 ≤ 1 / (2 * p) := by positivity
  have hf : 0 ≤ Real.rpow (d.factorial : ℝ) p := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (ENNReal.ofReal U).rpow (1 / (2 * p))
      ≤ (ENNReal.ofReal (Real.rpow (d.factorial : ℝ) p * C)).rpow (1 / (2 * p)) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) hr
    _ = (ENNReal.ofReal (Real.rpow (d.factorial : ℝ) p) * ENNReal.ofReal C).rpow (1 / (2 * p)) := by
        rw [ENNReal.ofReal_mul hf]
    _ = (ENNReal.ofReal (Real.rpow (d.factorial : ℝ) p)).rpow (1 / (2 * p)) *
          (ENNReal.ofReal C).rpow (1 / (2 * p)) := ENNReal.mul_rpow_of_nonneg _ _ hr
    _ = _ := by
        congr 1
        change (ENNReal.ofReal (Real.rpow (d.factorial : ℝ) p)) ^ (1 / (2 * p)) = _
        rw [ENNReal.ofReal_rpow_of_nonneg hf hr]
        congr 1
        unfold sqrtFact
        rw [Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_mul (Nat.cast_nonneg _)]
        congr 1
        field_simp

theorem series_sq_le (w X Y : ℕ → ℝ≥0∞) (D c : ℝ≥0∞) (h : ∀ k, X k ≤ c * Y k) :
    (D * ∑' k, w k * X k) ^ 2 ≤ c ^ 2 * D ^ 2 * (∑' k, w k * Y k) ^ 2 := by
  have h1 : ∑' k, w k * X k ≤ c * ∑' k, w k * Y k := by
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    calc w k * X k ≤ w k * (c * Y k) := mul_le_mul_right (h k) _
      _ = c * (w k * Y k) := by ring
  calc (D * ∑' k, w k * X k) ^ 2 ≤ (D * (c * ∑' k, w k * Y k)) ^ 2 :=
        pow_le_pow_left' (mul_le_mul_right h1 _) 2
    _ = _ := by ring

theorem const_eq {d : ℕ} {s : ℝ} (hs : 0 < s) :
    ENNReal.ofReal (sqrtFact d) ^ 2 * ENNReal.ofReal (1 - Real.rpow 3 (-s)) ^ 2 =
      ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2) := by
  have hdec : Real.rpow 3 (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  have hn : 0 ≤ 1 - Real.rpow 3 (-s) := sub_nonneg.2 hdec.le
  rw [← ENNReal.ofReal_pow (sqrtFact_nonneg d), ← ENNReal.ofReal_pow hn,
    ← ENNReal.ofReal_mul (pow_nonneg (sqrtFact_nonneg d) 2), sqrtFact_sq]

theorem upper_le {d : ℕ} (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hA : ∀ i j, Integrable (fun x => a x i j) (volume.restrict (originCube 1)))
    {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    upperMoment a ha s p hs hp ≤
      ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-s)) ^ 2) *
        besovCubeNorm a hA s p hs hp := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hlev (k : ℕ) : (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / (2 * p)) ≤
      ENNReal.ofReal (sqrtFact d) * (ENNReal.ofReal (cubeMean a k p)).rpow (1 / (2 * p)) := by
    have h1 := Besov.upperCellAverage_le_matrixCellPowerAverage a ha k p hp
    have h2 : upperCellAverage a ha k p ≤
        ((triangulation (d := d) k).attach.sum fun η =>
          Real.rpow ‖volumeAverageMat (simplexCell k η) a‖ p) /
        ((triangulation (d := d) k).card : ℝ) := h1
    refine root_le hp0 ?_ (h2.trans (simplexSum_le a ha k hp))
    unfold cubeMean
    exact div_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))
      (Nat.cast_nonneg _)
  unfold upperMoment besovCubeNorm
  have := series_sq_le (fun k : ℕ => ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))))
    (fun k => (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / (2 * p)))
    (fun k => (ENNReal.ofReal (cubeMean a k p)).rpow (1 / (2 * p)))
    (ENNReal.ofReal (1 - Real.rpow 3 (-s))) (ENNReal.ofReal (sqrtFact d)) hlev
  rw [← const_eq hs]
  exact this

theorem lowerMoment_inv_eq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (t q : ℝ) (ht : 0 < t) (hq : 1 ≤ q) :
    (lowerMoment a ha t q ht hq)⁻¹ =
      (ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))) ^ 2 := by
  unfold lowerMoment
  change ((_ ^ (-2 : ℝ))⁻¹ : ℝ≥0∞) = _
  rw [ENNReal.rpow_neg, inv_inv]
  exact ENNReal.rpow_ofNat _ 2

theorem lower_le {d : ℕ} (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hAinv : ∀ i j, Integrable (fun x => (a x)⁻¹ i j) (volume.restrict (originCube 1)))
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q) :
    (lowerMoment a ha t q ht hq)⁻¹ ≤
      ENNReal.ofReal ((d.factorial : ℝ) * (1 - Real.rpow 3 (-t)) ^ 2) *
        besovCubeNorm (fun x => (a x)⁻¹) hAinv t q ht hq := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hlev (k : ℕ) : (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)) ≤
      ENNReal.ofReal (sqrtFact d) *
        (ENNReal.ofReal (cubeMean (fun x => (a x)⁻¹) k q)).rpow (1 / (2 * q)) := by
    have h1 := Besov.lowerCellAverage_le_matrixCellPowerAverage a ha k q hq
    have h2 : lowerCellAverage a ha k q ≤
        ((triangulation (d := d) k).attach.sum fun η =>
          Real.rpow ‖volumeAverageMat (simplexCell k η) (fun x => (a x)⁻¹)‖ q) /
        ((triangulation (d := d) k).card : ℝ) := h1
    refine root_le hq0 ?_ (h2.trans (simplexSum_le _ (Weighted.response_inverse_coefficient ha) k hq))
    unfold cubeMean
    exact div_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) _))
      (Nat.cast_nonneg _)
  rw [lowerMoment_inv_eq]
  unfold besovCubeNorm
  have := series_sq_le (fun k : ℕ => ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))))
    (fun k => (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)))
    (fun k => (ENNReal.ofReal (cubeMean (fun x => (a x)⁻¹) k q)).rpow (1 / (2 * q)))
    (ENNReal.ofReal (1 - Real.rpow 3 (-t))) (ENNReal.ofReal (sqrtFact d)) hlev
  rw [← const_eq ht]
  exact this

end CoarseDeGiorgi.CoefficientConditions
