import CoarseDeGiorgi.Endpoint.CubeInterface
import CoarseDeGiorgi.Harnack.Moments.MomentComparison

/-! Absorption of fixed constants and path lengths into the Harnack exponential. -/
namespace CoarseDeGiorgi.Endpoint
open Homogenization MeasureTheory
open scoped ENNReal

theorem chaining_sqrt_contrast_ge_one {d : ℕ} (hd : 1 ≤ d)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    {p q s t : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 0 < s) (ht : 0 < t)
    (hU : upperMoment a ha s p hs hp < ⊤) (hL : 0 < lowerMoment a ha t q ht hq) :
    1 ≤ Real.sqrt (contrast a ha s t p q hs ht hp hq).toReal := by
  have hfin : contrast a ha s t p q hs ht hp hq ≠ ⊤ := ENNReal.div_ne_top hU.ne hL.ne'
  have hone := Harnack.Moments.moment_contrast_ge_one hd a ha hs ht hp hq hU hL
  have hr : 1 ≤ (contrast a ha s t p q hs ht hp hq).toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hfin hone
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr

theorem chaining_exp_pow (C X : ℝ) (n : ℕ) :
    (ENNReal.ofReal (Real.exp (C * X))) ^ n =
      ENNReal.ofReal (Real.exp (((n : ℝ) * C) * X)) := by
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  ring

theorem chaining_absorb (K : ℝ≥0∞) (hK : K ≠ ⊤) (C X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    K * (ENNReal.ofReal (Real.exp (C * X))) ^ n ≤
      ENNReal.ofReal (Real.exp ((K.toReal + (n : ℝ) * C) * X)) := by
  have hKX : K.toReal ≤ K.toReal * X := by
    exact le_mul_of_one_le_right ENNReal.toReal_nonneg hX
  have hKexp : K.toReal ≤ Real.exp (K.toReal * X) :=
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)).trans (Real.exp_le_exp.mpr hKX)
  rw [chaining_exp_pow]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (K.toReal * X)) *
        ENNReal.ofReal (Real.exp (((n : ℝ) * C) * X)) := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      calc
        K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hKexp
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring

end CoarseDeGiorgi.Endpoint
