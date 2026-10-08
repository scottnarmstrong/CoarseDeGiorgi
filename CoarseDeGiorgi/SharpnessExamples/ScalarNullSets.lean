module

public import CoarseDeGiorgi.SharpnessExamples.ScalarBandGeometry
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Null interfaces for translated cylinders -/

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

theorem transverseNorm_flatJoin {m : ℕ} (t : ℝ) (y : Vec m) :
    transverseNorm (flatJoin t y) = Foundations.Euclid.eNorm2 y := by
  unfold transverseNorm euclideanNorm Foundations.Euclid.eNorm2 vecNormSq vecDot
  simp only [Fin.sum_univ_succ, transversePart, flatJoin, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, ite_true, Nat.succ_ne_zero, ite_false, zero_mul, zero_add]

/-- Every positive transverse radius sphere is a volume-null cylinder
interface, even before restriction to the cube. -/
theorem transverseNorm_sphere_null {m : ℕ} {r : ℝ} (hr : r ≠ 0) :
    volume {x : Vec (m + 1) | transverseNorm x = r} = 0 := by
  let E := {y : Vec m | Foundations.Euclid.eNorm2 y = r}
  have hE : MeasurableSet E :=
    isClosed_eq Foundations.Euclid.continuous_eNorm2 continuous_const |>.measurableSet
  have hTail : volume E = 0 := by
    have hpre : WithLp.toLp 2 ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) r = E := by
      ext y
      simp only [mem_preimage, Metric.mem_sphere, dist_zero_right, mem_ofPred_eq, E,
        ← Foundations.Euclid.eNorm2_eq_norm_toLp]
    rw [← hpre, (PiLp.volume_preserving_toLp (Fin m)).measure_preimage
      Metric.isClosed_sphere.measurableSet.nullMeasurableSet]
    exact Measure.addHaar_sphere_of_ne_zero volume 0 hr
  let S := {x : Vec (m + 1) | transverseNorm x = r}
  have hS : MeasurableSet S := isClosed_eq lineRadius_continuous continuous_const |>.measurableSet
  have hpre : (fun ty : ℝ × Vec m => flatJoin ty.1 ty.2) ⁻¹' S = univ ×ˢ E := by
    ext ty
    simp only [S, E, mem_preimage, mem_ofPred_eq, transverseNorm_flatJoin,
      mem_prod, mem_univ, true_and]
  rw [← volume_preserving_flatJoin.measure_preimage hS.nullMeasurableSet,
    hpre, Measure.prod_prod, hTail, mul_zero]

theorem shifted_transverseNorm_ne_ae {m : ℕ} (c : Vec (m + 1)) {r : ℝ} (hr : r ≠ 0) :
    ∀ᵐ x : Vec (m + 1) ∂volume, transverseNorm (x - c) ≠ r := by
  have h : ∀ᵐ x : Vec (m + 1) ∂volume, transverseNorm x ≠ r := by
    rw [ae_iff]
    simpa only [not_not] using transverseNorm_sphere_null (m := m) hr
  exact (measurePreserving_sub_right volume c).quasiMeasurePreserving.ae h

theorem shifted_transverseNorm_pos_ae {d : ℕ} (hd : 2 ≤ d) (c : Vec d) :
    ∀ᵐ x : Vec d ∂volume, 0 < transverseNorm (x - c) :=
  (measurePreserving_sub_right volume c).quasiMeasurePreserving.ae (lineRadius_pos_ae hd)

end CoarseDeGiorgi.SharpnessExamples
