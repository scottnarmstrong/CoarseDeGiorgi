import CoarseDeGiorgi.Statements.NormalizedLpMoment
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- The normalized ENNReal moment `normalizedLpMoment` is the volume-normalized `eLpNorm'`
quasi-norm, for arbitrary positive exponents.
-/
theorem normalizedLpMoment_eq_eLpNorm' {d : ℕ} (V : Set (Vec d))
    (f : Vec d → ℝ) {b : ℝ} (hb : 0 < b) :
    CoarseDeGiorgi.normalizedLpMoment b hb V f =
      (volume.restrict V Set.univ) ^ (-1 / b) *
        eLpNorm' f b (volume.restrict V) := by
  unfold CoarseDeGiorgi.normalizedLpMoment
  rw [eLpNorm'_eq_lintegral_enorm]
  have hmeasure : volume V = volume.restrict V Set.univ := by simp
  rw [hmeasure]
  simp only [Real.enorm_eq_ofReal_abs]
  simp only [← ENNReal.rpow_eq_pow]
  calc
    _ = (volume.restrict V Set.univ)⁻¹ ^ (1 / b) *
          (∫⁻ x in V, (ENNReal.ofReal |f x|).rpow b) ^ (1 / b) := by
            rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / b)]
            rfl
    _ = _ := by
      rw [show (-1 / b : ℝ) = -(1 / b) by ring,
        ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      rfl

/-- Normalized moments are monotone in positive exponents on any set of
positive finite volume, without assuming the larger exponent is at least one.
-/
theorem normalizedLpMoment_mono {d : ℕ} (V : Set (Vec d))
    (f : Vec d → ℝ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f (volume.restrict V))
    (hVpos : 0 < volume V) (hVtop : volume V ≠ ⊤) :
    CoarseDeGiorgi.normalizedLpMoment p hp V f ≤
      CoarseDeGiorgi.normalizedLpMoment q (lt_of_lt_of_le hp hpq) V f := by
  rw [normalizedLpMoment_eq_eLpNorm' V f hp,
    normalizedLpMoment_eq_eLpNorm' V f (lt_of_lt_of_le hp hpq)]
  let m := volume.restrict V Set.univ
  have hm0 : m ≠ 0 := ne_of_gt (by simpa [m] using hVpos)
  have hmtop : m ≠ ⊤ := by simpa [m] using hVtop
  have hraw := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp hpq hf
  change m ^ (-1 / p) * eLpNorm' f p (volume.restrict V) ≤
    m ^ (-1 / q) * eLpNorm' f q (volume.restrict V)
  calc
    m ^ (-1 / p) * eLpNorm' f p (volume.restrict V) ≤
        m ^ (-1 / p) *
          (eLpNorm' f q (volume.restrict V) * m ^ (1 / p - 1 / q)) := by
      gcongr
    _ = (m ^ (-1 / p) * m ^ (1 / p - 1 / q)) *
          eLpNorm' f q (volume.restrict V) := by ac_rfl
    _ = m ^ (-1 / q) * eLpNorm' f q (volume.restrict V) := by
      rw [← ENNReal.rpow_add (-1 / p) (1 / p - 1 / q) hm0 hmtop]
      congr 2
      ring

end CoarseDeGiorgi.Harnack.Iterations
