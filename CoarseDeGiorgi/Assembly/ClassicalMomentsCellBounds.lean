module

public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import CoarseDeGiorgi.Weighted.ResponseBoundsMoments
public import CoarseDeGiorgi.Weighted.UpperSpecNorm
public import CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

namespace CoarseDeGiorgi.Assembly.ClassicalMomentsImpl

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- A finite classical moment supplies both Bochner and power integrability. -/
theorem classical_integrability {d : ℕ} {A : Vec d → Mat d} {p : ℝ}
    (hp : 1 ≤ p) (hA : AEStronglyMeasurable A (volume.restrict (originCube 1)))
    (hLp : eLpNorm (fun x => ‖A x‖) (ENNReal.ofReal p)
      (volume.restrict (originCube 1)) < ⊤) :
    IntegrableOn A (originCube 1) ∧
      IntegrableOn (fun x => ‖A x‖ ^ p) (originCube 1) := by
  have : IsFiniteMeasure (volume.restrict (originCube (d := d) 1)) :=
    ⟨by simp [originCube_volume_one]⟩
  have hmem : MemLp A (ENNReal.ofReal p) (volume.restrict (originCube 1)) := by
    simpa only [memLp_iff, eLpNorm_norm A hA] using hLp
  refine ⟨hmem.integrable (by simpa using ENNReal.ofReal_le_ofReal hp), ?_⟩
  change Integrable (fun x => ‖A x‖ ^ p) (volume.restrict (originCube 1))
  simpa only [ENNReal.toReal_ofReal (zero_le_one.trans hp)] using
    hmem.integrable_norm_rpow (by simp [zero_lt_one.trans_le hp]) ENNReal.ofReal_ne_top

/-- The classical norm is the p-th root of the real power integral. -/
theorem classical_eLpNorm_eq {d : ℕ} {A : Vec d → Mat d} {p : ℝ}
    (hp : 0 < p) (hA : AEStronglyMeasurable A (volume.restrict (originCube 1)))
    (hAp : IntegrableOn (fun x => ‖A x‖ ^ p) (originCube 1)) :
    eLpNorm (fun x => ‖A x‖) (ENNReal.ofReal p) (volume.restrict (originCube 1)) =
      (ENNReal.ofReal (∫ x in originCube 1, ‖A x‖ ^ p)).rpow (1 / p) := by
  rw [eLpNorm_norm A hA, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by simp [hp]) ENNReal.ofReal_ne_top hA, ENNReal.toReal_ofReal hp.le]
  simp_rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [← ofReal_integral_eq_lintegral_ofReal hAp
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p)]
  rfl

/-- Cellwise response norm bounds and Jensen give the normalized level comparison. -/
theorem classical_level_bound {d : ℕ} (k : ℕ) {A : Vec d → Mat d} {p : ℝ}
    (hp : 1 ≤ p) (hA : IntegrableOn A (originCube 1))
    (hAp : IntegrableOn (fun x => ‖A x‖ ^ p) (originCube 1))
    (R : SimplexIndex d k → Mat d)
    (hR : ∀ η, ‖R η‖ ≤ ‖volumeAverageMat (simplexCell k η) A‖) :
    ((triangulation (d := d) k).attach.sum fun η => Real.rpow ‖R η‖ p) /
      ((triangulation (d := d) k).card : ℝ) ≤ ∫ x in originCube 1, ‖A x‖ ^ p := by
  classical
  rw [← partition_average k hAp]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro η _
  apply (Real.rpow_le_rpow (norm_nonneg _) (hR η) (zero_le_one.trans hp)).trans
  have hV := simplexCell_isOpenBoundedConvexDomain k η
  exact Weighted.classical_matrix_moment_bound hp
    (hV.isOpen.measure_pos volume (simplexCell_nonempty k η)).ne'
    hV.isBoundedDomain.isBounded.measure_lt_top.ne
    (hA.mono_set (CoarseDeGiorgi.simplexCell_subset_originCube k η))
    (hAp.mono_set (CoarseDeGiorgi.simplexCell_subset_originCube k η))

theorem upperCellAverage_bound {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {p : ℝ} (hp : 1 ≤ p)
    (hLp : eLpNorm (fun x => ‖a x‖) (ENNReal.ofReal p)
      (volume.restrict (originCube 1)) < ⊤) (k : ℕ) :
    upperCellAverage a ha k p ≤ ∫ x in originCube 1, ‖a x‖ ^ p := by
  obtain ⟨hi, hip⟩ := classical_integrability hp ha.1 hLp
  apply classical_level_bound k hp hi hip (upperResponseOnCell k a ha)
  intro η
  exact Weighted.UpperResponseImpl.upperResponse_norm_le
    (simplexCell_isOpenBoundedConvexDomain k η) (simplexCell_nonempty k η)
    (weightedCoeffOn_simplexCell k a ha η)


end CoarseDeGiorgi.Assembly.ClassicalMomentsImpl
