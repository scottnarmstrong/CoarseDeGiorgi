module

public import CoarseDeGiorgi.SharpnessExamples.ScalarSeries
public import CoarseDeGiorgi.SharpnessExamples.BesovCubeSimplex

/-! # The cube quasi-norm of a positive field dominated by a series of cylinders

Per level, the power mean over triadic cubes is at most the power mean over simplices, which
is controlled by Minkowski's inequality for the series. Square-root subadditivity and the
summed bound per cylinder then control the sum over levels.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

/-- Square-root subadditivity for a series with summable square roots. -/
theorem sqrt_tsum_le_tsum_sqrt {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n)
    (hy : Summable (fun n => Real.sqrt (x n))) :
    Real.sqrt (∑' n, x n) ≤ ∑' n, Real.sqrt (x n) := by
  have hsq : ∀ s : Finset ℕ, ∑ n ∈ s, x n ≤ (∑' n, Real.sqrt (x n)) ^ 2 := by
    intro s
    have hind : ∀ s : Finset ℕ, ∑ n ∈ s, x n ≤ (∑ n ∈ s, Real.sqrt (x n)) ^ 2 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        have h1 : 0 ≤ ∑ n ∈ s, Real.sqrt (x n) := Finset.sum_nonneg fun n _ => Real.sqrt_nonneg _
        have h2 : x a = Real.sqrt (x a) ^ 2 := (Real.sq_sqrt (hx a)).symm
        nlinarith [Real.sqrt_nonneg (x a), mul_nonneg (Real.sqrt_nonneg (x a)) h1]
    refine (hind s).trans ?_
    have hle : ∑ n ∈ s, Real.sqrt (x n) ≤ ∑' n, Real.sqrt (x n) :=
      hy.sum_le_tsum s (fun n _ => Real.sqrt_nonneg _)
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => Real.sqrt_nonneg _) hle 2
  have htot : ∑' n, x n ≤ (∑' n, Real.sqrt (x n)) ^ 2 :=
    Real.tsum_le_of_sum_le hx hsq
  have h0 : 0 ≤ ∑' n, Real.sqrt (x n) := tsum_nonneg fun n => Real.sqrt_nonneg _
  calc Real.sqrt (∑' n, x n) ≤ Real.sqrt ((∑' n, Real.sqrt (x n)) ^ 2) := Real.sqrt_le_sqrt htot
    _ = _ := Real.sqrt_sq h0

private theorem avg_nonneg {d : ℕ} (V : Set (Vec d)) {f : Vec d → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ volumeAverage V f := by
  unfold volumeAverage
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg hf)

private theorem simplex_avg_one {d k : ℕ} (η : SimplexIndex d k) :
    volumeAverage (simplexCell k η) (fun _ => (1 : ℝ)) = 1 := by
  apply volumeAverage_const
  have hpos : 0 < (volume (simplexCell k η)).toReal := by
    rw [Assembly.ClassicalMomentsImpl.simplexCell_volume_real]
    exact inv_pos.mpr (by exact_mod_cast Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)
  exact hpos.ne'

private theorem simplex_integral_summable {d k : ℕ}
    (η : SimplexIndex d k) {f : ℕ → Vec d → ℝ}
    (hf : ∀ j, IntegrableOn (f j) (originCube 1) volume)
    (hs : Summable (fun j => ∫ x in originCube 1, ‖f j x‖ ∂volume)) :
    Summable (fun j => ∫ x in simplexCell k η, ‖f j x‖ ∂volume) := by
  apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun x => norm_nonneg _))
    (fun j => integral_mono_measure
      (Measure.restrict_mono (simplexCell_subset_originCube k η) le_rfl)
      (Filter.Eventually.of_forall (fun x => norm_nonneg _)) (hf j).norm)
    hs

/-- Minkowski for the simplex power mean of a field dominated by `1 + ∑ f_j`. -/
theorem simplexMean_le_one_add_series {d : ℕ} (k : ℕ)
    (w : Vec d → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw : IntegrableOn w (originCube 1) volume)
    (f : ℕ → Vec d → ℝ) (hf0 : ∀ j x, 0 ≤ f j x)
    (hf : ∀ j, IntegrableOn (f j) (originCube 1) volume)
    (hs : Summable (fun j => ∫ x in originCube 1, ‖f j x‖ ∂volume))
    (hmaj : ∀ x, w x ≤ 1 + ∑' j, f j x) {v : ℝ} (hv : 1 ≤ v)
    (haMean : Summable (fun j =>
      finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) (f j)) v)) :
    finitePowerMean (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) w) v ≤
      1 + ∑' j, finitePowerMean
        (fun η : SimplexIndex d k => volumeAverage (simplexCell k η) (f j)) v := by
  classical
  have hsumInt := integrable_tsum_of_summable_integral_norm hf hs
  have hcube : volume (originCube (d := d) 1) ≠ ⊤ := by
    rw [Assembly.ClassicalMomentsImpl.originCube_volume_one d]
    simp
  have hone : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (originCube 1) volume :=
    integrableOn_const hcube
  let a : ℕ → SimplexIndex d k → ℝ := fun j η => volumeAverage (simplexCell k η) (f j)
  have ha0 : ∀ j η, 0 ≤ a j η := fun j η => avg_nonneg _ (hf0 j)
  have haSum : ∀ η, Summable (fun j => a j η) := by
    intro η
    have hi := simplex_integral_summable (k := k) η hf hs
    have hnorm : ∀ j, (∫ x in simplexCell k η, ‖f j x‖ ∂volume) =
        ∫ x in simplexCell k η, f j x ∂volume := by
      intro j
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => Real.norm_of_nonneg (hf0 j x))
    simp only [hnorm] at hi
    exact hi.mul_left ((volume (simplexCell k η)).toReal)⁻¹
  have havg : ∀ η : SimplexIndex d k,
      volumeAverage (simplexCell k η) w ≤ 1 + ∑' j, a j η := by
    intro η
    have hsub := simplexCell_subset_originCube k η
    have hwcell := hw.mono_set hsub
    have hsumcell := hsumInt.mono_measure (Measure.restrict_mono hsub le_rfl)
    have honecell := hone.mono_set hsub
    have hmono : volumeAverage (simplexCell k η) w ≤
        volumeAverage (simplexCell k η) (fun x => 1 + ∑' j, f j x) := by
      unfold volumeAverage
      apply mul_le_mul_of_nonneg_left
        (integral_mono_ae hwcell (honecell.add hsumcell)
          (Filter.Eventually.of_forall hmaj)) (inv_nonneg.mpr ENNReal.toReal_nonneg)
    have hsum := volumeAverage_tsum_of_summable_integral_norm (simplexCell k η) f
      (fun j => (hf j).mono_set hsub) (simplex_integral_summable η hf hs)
    have hadd := volumeAverage_add honecell hsumcell
    change volumeAverage (simplexCell k η) (fun x => 1 + ∑' j, f j x) = _ at hadd
    rw [hadd, simplex_avg_one η, hsum] at hmono
    exact hmono
  have : Nonempty (SimplexIndex d k) := by
    change Nonempty {η // η ∈ triangulation k}
    exact (Finset.card_pos.mp (Assembly.ClassicalMomentsImpl.triangulation_card_pos d k)).coe_sort
  calc
    _ ≤ finitePowerMean (fun η => 1 + ∑' j, a j η) v :=
      finitePowerMean_mono (fun η => avg_nonneg _ hw0) havg
        (zero_lt_one.trans_le hv)
    _ ≤ finitePowerMean (fun _ : SimplexIndex d k => (1 : ℝ)) v +
        finitePowerMean (fun η => ∑' j, a j η) v :=
      finitePowerMean_add_le _ _ (fun _ => by norm_num)
        (fun η => tsum_nonneg (fun j => ha0 j η)) hv
    _ = 1 + finitePowerMean (fun η => ∑' j, a j η) v := by
      rw [finitePowerMean_const (by norm_num : (0 : ℝ) ≤ 1) (zero_lt_one.trans_le hv)]
    _ ≤ 1 + ∑' j, finitePowerMean (a j) v :=
      add_le_add le_rfl (finitePowerMean_tsum_le a ha0 haSum hv haMean)

end CoarseDeGiorgi.SharpnessExamples
