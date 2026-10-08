import CoarseDeGiorgi.Assembly.ClassicalMomentsSeries
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Harnack.Moments.LevelMeans

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem normalized_series_ge {s : ℝ} (hs : 0 < s)
    (c : ℝ≥0∞) (b : ℕ → ℝ≥0∞) (hb : ∀ k, c ≤ b k) :
    c ≤ ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * b k) := by
  have hseries :
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * c) ≤
        ∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * b k := by
    apply ENNReal.tsum_le_tsum
    intro k
    exact mul_le_mul_right (hb k) _
  have hconst : c = ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
      (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * s))) * c) := by
    rw [ENNReal.tsum_mul_right, ← mul_assoc,
      Assembly.ClassicalMomentsImpl.geometric_normalization hs]
    simp
  rw [hconst]
  exact mul_le_mul_right hseries _

private theorem halfPower_sq (x : ℝ≥0∞) :
    (x.rpow (1 / 2)) ^ 2 = x := by
  simpa using Assembly.ClassicalMomentsImpl.half_power_sq x (p := 1) (by norm_num)

private theorem level_halfpower_le_upper {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {p : ℝ} (hp : 1 ≤ p) :
    (ENNReal.ofReal (‖upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow
        (1 / 2) ≤
      (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  have hlevel := upper_level_mean hd k a ha hp
  have hpowCoeff : (ENNReal.ofReal (‖upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow p =
      ENNReal.ofReal (Real.rpow (‖upperResponse a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖) p) :=
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
  have hlevel' : (ENNReal.ofReal (‖upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow p ≤
      ENNReal.ofReal (upperCellAverage a ha k p) := by
    rw [hpowCoeff]
    exact ENNReal.ofReal_le_ofReal hlevel
  have hr := ENNReal.rpow_le_rpow hlevel' (by positivity : 0 ≤ 1 / (2 * p))
  calc
    _ = ((ENNReal.ofReal (‖upperResponse a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow p).rpow
          (1 / (2 * p)) := by
      have hexp : (1 : ℝ) / 2 = p * (1 / (2 * p)) := by field_simp
      rw [hexp]
      exact ENNReal.rpow_mul _ _ _
    _ ≤ _ := hr

private theorem level_halfpower_le_lower {d : ℕ} (hd : 1 ≤ d) (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {q : ℝ} (hq : 1 ≤ q) :
    (ENNReal.ofReal (‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow
        (1 / 2) ≤
      (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)) := by
  have hq0 : 0 < q := by linarith
  have hlevel := lower_level_mean hd k a ha hq
  have hpowCoeff : (ENNReal.ofReal (‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow q =
      ENNReal.ofReal (Real.rpow (‖lowerResponseInv a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖) q) :=
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0.le
  have hlevel' : (ENNReal.ofReal (‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow q ≤
      ENNReal.ofReal (lowerCellAverage a ha k q) := by
    rw [hpowCoeff]
    exact ENNReal.ofReal_le_ofReal hlevel
  have hr := ENNReal.rpow_le_rpow hlevel' (by positivity : 0 ≤ 1 / (2 * q))
  calc
    _ = ((ENNReal.ofReal (‖lowerResponseInv a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow q).rpow
          (1 / (2 * q)) := by
      have hexp : (1 : ℝ) / 2 = q * (1 / (2 * q)) := by field_simp
      rw [hexp]
      exact ENNReal.rpow_mul _ _ _
    _ ≤ _ := hr

/-- The norm of the upper response on the unit cube is at most the upper moment. -/
theorem upperMoment_ge_wholeResponse {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    ENNReal.ofReal ‖upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ ≤
        upperMoment a ha s p hs hp := by
  let c := (ENNReal.ofReal (‖upperResponse a (originCube 1)
    LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow (1 / 2)
  let b := fun k : ℕ => (ENNReal.ofReal (upperCellAverage a ha k p)).rpow (1 / (2 * p))
  have hb : ∀ k, c ≤ b k := by
    intro k
    exact level_halfpower_le_upper hd k a ha hp
  have hsrs := normalized_series_ge hs c b hb
  have hp0 : 0 < p := by linarith
  have hsq : c ^ 2 = ENNReal.ofReal (‖upperResponse a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖) := by
    dsimp [c]
    exact halfPower_sq _
  rw [upperMoment]
  dsimp [b] at hsrs ⊢
  rw [← hsq]
  exact pow_le_pow_left' hsrs 2

/-- The norm of the inverse lower response on the unit cube is at most the inverse lower
moment. -/
theorem lowerMoment_inv_ge_wholeResponse {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q) :
    (lowerMoment a ha t q ht hq)⁻¹ ≥
      ENNReal.ofReal ‖lowerResponseInv a (originCube 1)
        LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖ := by
  let c := (ENNReal.ofReal (‖lowerResponseInv a (originCube 1)
    LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖)).rpow (1 / 2)
  let b := fun k : ℕ => (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q))
  have hb : ∀ k, c ≤ b k := by
    intro k
    exact level_halfpower_le_lower hd k a ha hq
  have hsrs := normalized_series_ge ht c b hb
  have hsq : c ^ 2 = ENNReal.ofReal (‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖) := by
    dsimp [c]
    exact halfPower_sq _
  let S := ENNReal.ofReal (1 - Real.rpow 3 (-t)) *
    (∑' k : ℕ, ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) * b k)
  have hmain : ENNReal.ofReal (‖lowerResponseInv a (originCube 1)
      LowerFractional.lower_unitCube_domain LowerFractional.lower_unitCube_nonempty ha‖) ≤
        S ^ 2 := by
    rw [← hsq]
    dsimp [S] at hsrs ⊢
    exact pow_le_pow_left' hsrs 2
  have hmoment : lowerMoment a ha t q ht hq =
      S.rpow (-2) := rfl
  rw [hmoment]
  have hneg : S.rpow (-2) = (S.rpow 2)⁻¹ := ENNReal.rpow_neg S 2
  have hinv : (S.rpow (-2))⁻¹ = S ^ 2 := by rw [hneg]; simp
  rw [hinv]
  exact hmain

end CoarseDeGiorgi.Harnack.Moments
