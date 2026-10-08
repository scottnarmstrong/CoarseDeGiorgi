import CoarseDeGiorgi.Harnack.Iterations.EssentialLimit
import CoarseDeGiorgi.Harnack.Iterations.NormalizedMomentOrder

open Homogenization MeasureTheory Filter
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Uniform normalized moment bounds on nested, volume-controlled domains imply
the essential-supremum bound on the fixed inner domain.
-/
theorem eLpNormEssSup_le_of_uniform_normalizedMoments_on_nested_sets
    {d : ℕ} (V : Set (Vec d)) (Vn : ℕ → Set (Vec d)) (f : Vec d → ℝ)
    {A D : ℝ≥0∞}
    (hVpos : 0 < volume V) (hVtop : volume V ≠ ⊤)
    (hApos : 0 < A) (hAtop : A ≠ ⊤)
    (hDpos : 0 < D) (hDtop : D ≠ ⊤)
    (hsubset : ∀ n, V ⊆ Vn n)
    (hvolume : ∀ n, volume (Vn n) ≤ D * volume V)
    (p : ℕ → ℝ) (hp : ∀ n, 0 < p n)
    (hpTop : Filter.Tendsto p Filter.atTop Filter.atTop)
    (hmeas : ∀ n, MeasureTheory.AEStronglyMeasurable f
      (volume.restrict (Vn n)))
    (hbound : ∀ n, CoarseDeGiorgi.normalizedLpMoment (p n) (hp n)
      (Vn n) f ≤ A) :
    MeasureTheory.eLpNormEssSup f (volume.restrict V) ≤ A := by
  have hVmeasure : (volume.restrict V) Set.univ = volume V := by simp
  have hμtop : (volume.restrict V) Set.univ ≠ ⊤ := by
    simpa [hVmeasure] using hVtop
  have hf : AEStronglyMeasurable f (volume.restrict V) := by
    have hrestrict : volume.restrict V ≤ volume.restrict (Vn 0) :=
      Measure.restrict_mono (hsubset 0) le_rfl
    exact AEStronglyMeasurable.mono_measure (hmeas 0) hrestrict
  let K : ℝ≥0∞ := D * volume V
  have hKpos : 0 < K := by
    dsimp [K]
    exact ENNReal.mul_pos (ne_of_gt hDpos) (ne_of_gt hVpos)
  have hKtop : K ≠ ⊤ := by
    dsimp [K]
    exact (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hDtop)
      (lt_top_iff_ne_top.mpr hVtop)).ne
  have hLpBound (n : ℕ) :
      eLpNorm' f (p n) (volume.restrict V) ≤ A * K ^ (1 / p n) := by
    have hvpos : 0 < volume (Vn n) :=
      lt_of_lt_of_le hVpos (measure_mono (hsubset n))
    have hvtop : volume (Vn n) ≠ ⊤ := by
      apply ne_of_lt
      exact (hvolume n).trans_lt
        (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hDtop)
          (lt_top_iff_ne_top.mpr hVtop))
    have hmomentEq : CoarseDeGiorgi.normalizedLpMoment (p n) (hp n)
      (Vn n) f = (volume (Vn n)) ^ (-(1 / p n)) *
          eLpNorm' f (p n) (volume.restrict (Vn n)) := by
      rw [normalizedLpMoment_eq_eLpNorm' (Vn n) f (hp n)]
      rw [show (-1 / p n : ℝ) = -(1 / p n) by ring]
      simp
    have hmoment := hbound n
    rw [hmomentEq] at hmoment
    have hcancel : (volume (Vn n)) ^ (1 / p n) *
        (volume (Vn n)) ^ (-(1 / p n)) = 1 := by
      rw [← ENNReal.rpow_add (1 / p n) (-(1 / p n)) hvpos.ne' hvtop]
      simp
    have hnormVn : eLpNorm' f (p n) (volume.restrict (Vn n)) ≤
        (volume (Vn n)) ^ (1 / p n) * A := by
      calc
        eLpNorm' f (p n) (volume.restrict (Vn n)) =
            ((volume (Vn n)) ^ (1 / p n) *
              (volume (Vn n)) ^ (-(1 / p n))) *
                eLpNorm' f (p n) (volume.restrict (Vn n)) := by
          rw [hcancel]
          simp
        _ = (volume (Vn n)) ^ (1 / p n) *
              ((volume (Vn n)) ^ (-(1 / p n)) *
                eLpNorm' f (p n) (volume.restrict (Vn n))) := by ac_rfl
        _ ≤ (volume (Vn n)) ^ (1 / p n) * A :=
          mul_le_mul_of_nonneg_left hmoment zero_le
    have hroot : (volume (Vn n)) ^ (1 / p n) ≤ K ^ (1 / p n) := by
      exact ENNReal.rpow_le_rpow (hvolume n)
        (div_nonneg (by norm_num) (hp n).le)
    have hmeasure : volume.restrict V ≤ volume.restrict (Vn n) :=
      Measure.restrict_mono (hsubset n) le_rfl
    calc
      eLpNorm' f (p n) (volume.restrict V) ≤
          eLpNorm' f (p n) (volume.restrict (Vn n)) :=
        eLpNorm'_mono_measure f hmeasure (le_of_lt (hp n))
      _ ≤ (volume (Vn n)) ^ (1 / p n) * A := hnormVn
      _ ≤ K ^ (1 / p n) * A :=
        mul_le_mul_of_nonneg_right hroot zero_le
      _ = A * K ^ (1 / p n) := by ac_rfl
  exact eLpNormEssSup_le_of_uniform_rpowLpBound hμtop hf hApos hAtop
    hKpos hKtop p hp hpTop hLpBound

end CoarseDeGiorgi.Harnack.Iterations
