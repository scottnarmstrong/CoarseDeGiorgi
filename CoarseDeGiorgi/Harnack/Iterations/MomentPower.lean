import CoarseDeGiorgi.Statements.NormalizedLpMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Normalized moments are unchanged by almost-everywhere equality on a
measurable domain.
-/
theorem normalizedLpMoment_congr_ae {d : ℕ} (V : Set (Vec d))
    (hV : MeasurableSet V) (f g : Vec d → ℝ) {b : ℝ} (hb : 0 < b)
    (hfg : f =ᵐ[volume.restrict V] g) :
    CoarseDeGiorgi.normalizedLpMoment b hb V f =
      CoarseDeGiorgi.normalizedLpMoment b hb V g := by
  unfold CoarseDeGiorgi.normalizedLpMoment
  have hInt :
      (∫⁻ x in V, (ENNReal.ofReal |f x|).rpow b) =
        ∫⁻ x in V, (ENNReal.ofReal |g x|).rpow b := by
    rw [← lintegral_indicator hV, ← lintegral_indicator hV]
    apply lintegral_congr_ae
    have hfg' : ∀ᵐ x ∂(volume.restrict V), f x = g x := hfg
    rw [ae_restrict_iff' hV] at hfg'
    filter_upwards [hfg'] with x hx
    by_cases hxV : x ∈ V
    · simp [hxV, hx]
    · simp [hxV]
  rw [hInt]

/-- Taking a positive real power of a positive function scales the exponent of
its normalized moment by the same factor.
-/
theorem normalizedLpMoment_rpow_scale {d : ℕ} (V : Set (Vec d))
    (hV : MeasurableSet V) (f : Vec d → ℝ) {b s : ℝ}
    (hb : 0 < b) (hs : 0 < s)
    (hpos : ∀ᵐ x ∂(volume.restrict V), 0 < f x) :
    CoarseDeGiorgi.normalizedLpMoment b hb V (fun x => Real.rpow (f x) s) =
      (CoarseDeGiorgi.normalizedLpMoment (b * s) (mul_pos hb hs) V f) ^ s := by
  unfold CoarseDeGiorgi.normalizedLpMoment
  have hpos' : ∀ᵐ x ∂volume, x ∈ V → 0 < f x := by
    rw [ae_restrict_iff' hV] at hpos
    exact hpos
  have hInt :
      (∫⁻ x in V,
        (ENNReal.ofReal |Real.rpow (f x) s|).rpow b) =
        ∫⁻ x in V, (ENNReal.ofReal |f x|).rpow (b * s) := by
    rw [← lintegral_indicator hV, ← lintegral_indicator hV]
    apply lintegral_congr_ae
    filter_upwards [hpos'] with x hx
    by_cases hxV : x ∈ V
    · have hxpos := hx hxV
      have hpower :
          Real.rpow (Real.rpow (f x) s) b = Real.rpow (f x) (b * s) := by
        calc
          Real.rpow (Real.rpow (f x) s) b = Real.rpow (f x) (s * b) :=
            (Real.rpow_mul hxpos.le s b).symm
          _ = Real.rpow (f x) (b * s) := by rw [mul_comm]
      have houterPos : 0 < Real.rpow (f x) s := Real.rpow_pos_of_pos hxpos s
      simp only [Set.indicator_of_mem hxV, abs_of_pos houterPos,
        abs_of_pos hxpos]
      calc
        (ENNReal.ofReal (Real.rpow (f x) s)).rpow b =
            ENNReal.ofReal (Real.rpow (Real.rpow (f x) s) b) := by
              simpa only [ENNReal.rpow_eq_pow, Real.rpow_eq_pow] using
                ENNReal.ofReal_rpow_of_pos houterPos
        _ = ENNReal.ofReal (Real.rpow (f x) (b * s)) := by rw [hpower]
        _ = (ENNReal.ofReal (f x)).rpow (b * s) := by
              symm
              simpa only [ENNReal.rpow_eq_pow, Real.rpow_eq_pow] using
                ENNReal.ofReal_rpow_of_pos hxpos
    · simp only [Set.indicator_of_notMem hxV]
  rw [hInt]
  change ((volume V)⁻¹ *
      ∫⁻ x in V, (ENNReal.ofReal |f x|).rpow (b * s)).rpow (1 / b) =
    (((volume V)⁻¹ *
      ∫⁻ x in V, (ENNReal.ofReal |f x|).rpow (b * s)).rpow (1 / (b * s))) ^ s
  have hexp : 1 / b = (1 / (b * s)) * s := by
    field_simp
  rw [hexp]
  exact ENNReal.rpow_mul _ _ _

end CoarseDeGiorgi.Harnack.Iterations
