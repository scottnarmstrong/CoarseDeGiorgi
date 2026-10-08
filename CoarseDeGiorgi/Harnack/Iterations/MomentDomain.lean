module

public import CoarseDeGiorgi.Harnack.Iterations.NormalizedMomentOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Transfer a lower moment on a smaller domain to a higher moment on a larger
domain, retaining the exact ratio of the two volume normalizations.
-/
theorem normalizedLpMoment_subset_bound {d : ℕ} (E V : Set (Vec d))
    (f : Vec d → ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q)
    (hEV : E ⊆ V) (hf : AEStronglyMeasurable f (volume.restrict V))
    (hEpos : 0 < volume E) (hEtop : volume E ≠ ⊤)
    (hVpos : 0 < volume V) (hVtop : volume V ≠ ⊤) :
    CoarseDeGiorgi.normalizedLpMoment p hp E f ≤
      (volume E) ^ (-(1 / q)) * (volume V) ^ (1 / q) *
        CoarseDeGiorgi.normalizedLpMoment q hq V f := by
  have hμEV : volume.restrict E ≤ volume.restrict V :=
    Measure.restrict_mono hEV le_rfl
  have hfE : AEStronglyMeasurable f (volume.restrict E) :=
    AEStronglyMeasurable.mono_measure hf hμEV
  have hmoment := normalizedLpMoment_mono E f hp hpq hfE hEpos hEtop
  have hnormE := normalizedLpMoment_eq_eLpNorm' E f hq
  have hnormV := normalizedLpMoment_eq_eLpNorm' V f hq
  have hmeasureE : volume E = (volume.restrict E) Set.univ := by simp
  have hmeasureV : volume V = (volume.restrict V) Set.univ := by simp
  have hnormMono : eLpNorm' f q (volume.restrict E) ≤
      eLpNorm' f q (volume.restrict V) :=
    eLpNorm'_mono_measure f hμEV (le_of_lt hq)
  have hEfactor : 0 ≤ (volume E) ^ (-(1 / q)) := by positivity
  have hmV0 : volume V ≠ 0 := ne_of_gt hVpos
  have hmVtop : volume V ≠ ⊤ := hVtop
  have hcancel : (volume V) ^ (1 / q) * (volume V) ^ (-(1 / q)) = 1 := by
    rw [← ENNReal.rpow_add (1 / q) (-(1 / q)) hmV0 hmVtop]
    simp
  have hnormalV : CoarseDeGiorgi.normalizedLpMoment q hq V f =
      (volume V) ^ (-(1 / q)) * eLpNorm' f q (volume.restrict V) := by
    rw [hnormV, ← hmeasureV]
    congr 2
    ring
  have hnormV' : eLpNorm' f q (volume.restrict V) =
      (volume V) ^ (1 / q) * CoarseDeGiorgi.normalizedLpMoment q hq V f := by
    calc
      eLpNorm' f q (volume.restrict V) = 1 * eLpNorm' f q (volume.restrict V) :=
        (one_mul _).symm
      _ = ((volume V) ^ (1 / q) * (volume V) ^ (-(1 / q))) *
          eLpNorm' f q (volume.restrict V) := by rw [hcancel]
      _ = (volume V) ^ (1 / q) *
          ((volume V) ^ (-(1 / q)) * eLpNorm' f q (volume.restrict V)) := by ac_rfl
      _ = (volume V) ^ (1 / q) * CoarseDeGiorgi.normalizedLpMoment q hq V f := by
        rw [← hnormalV]
  calc
    CoarseDeGiorgi.normalizedLpMoment p hp E f ≤
        CoarseDeGiorgi.normalizedLpMoment q hq E f := hmoment
    _ = (volume E) ^ (-(1 / q)) * eLpNorm' f q (volume.restrict E) := by
      rw [hnormE, ← hmeasureE]
      congr 2
      ring
    _ ≤ (volume E) ^ (-(1 / q)) * eLpNorm' f q (volume.restrict V) :=
      mul_le_mul_of_nonneg_left hnormMono hEfactor
    _ = (volume E) ^ (-(1 / q)) * (volume V) ^ (1 / q) *
          CoarseDeGiorgi.normalizedLpMoment q hq V f := by
      rw [hnormV']
      ac_rfl

end CoarseDeGiorgi.Harnack.Iterations
