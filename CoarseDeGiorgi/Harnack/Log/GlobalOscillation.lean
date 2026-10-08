import CoarseDeGiorgi.Harnack.Log.FiniteCover
import CoarseDeGiorgi.Foundations.Reconstruction.Geometry
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace CoarseDeGiorgi.Harnack.Log

open Homogenization MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

def logOscillationDomain {d : ℕ} : Set (Vec d) := originCube (7 / 8 : ℝ)

def logGridMean {d : ℕ} (w : Vec d → ℝ) (z : Fin d → ℤ) : ℝ :=
  volumeAverage (auxCube 4 z) w

private def logGridDeviation {d : ℕ} (w : Vec d → ℝ) (z : Fin d → ℤ) :
    Vec d → ℝ := fun x => |w x - logGridMean w z|

private def logGridDeviationOn {d : ℕ} (w : Vec d → ℝ) (z : Fin d → ℤ) :
    Vec d → ℝ := (auxCube 4 z).indicator (logGridDeviation w z)

private theorem eLpNorm_sum_le_card_of_local_bounds {α ι : Type*}
    [MeasurableSpace α] {μ : Measure α} (p B : ℝ≥0∞) (hp : 1 ≤ p)
    (s : Finset ι) (f : ι → α → ℝ)
    (hLocal : ∀ i ∈ s, eLpNorm (f i) p μ ≤ B) :
    eLpNorm (fun x => ∑ i ∈ s, f i x) p μ ≤ (s.card : ℝ≥0∞) * B := by
  have heq : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp only [Finset.sum_apply]
  calc
    eLpNorm (fun x => ∑ i ∈ s, f i x) p μ =
        eLpNorm (∑ i ∈ s, f i) p μ := by rw [heq]
    _ ≤ ∑ i ∈ s, eLpNorm (f i) p μ := eLpNorm_sum_le hp
    _ ≤ ∑ _i ∈ s, B := by
      apply Finset.sum_le_sum
      intro i hi
      exact hLocal i hi
    _ = (s.card : ℝ≥0∞) * B := by simp

/-- Sum the local oscillations over the fixed finite cover.  The only inputs are
the local cube bounds and the dimension-only bound on each auxiliary mean
relative to a reference mean; the latter is supplied by neighboring-overlap
Holder estimates and the grid path construction.
-/
theorem log_global_oscillation_of_grid_bounds {d : ℕ} (r : ℝ) (hr : 1 ≤ r)
    (w : Vec d → ℝ)
    (hw : AEStronglyMeasurable w (volume.restrict (originCube (d := d) 1)))
    (z₀ : Fin d → ℤ) (B D : ℝ) (hD : 0 ≤ D)
    (hLocal : ∀ z ∈ fixedLogGrid,
      eLpNorm (fun x => w x - logGridMean w z) (ENNReal.ofReal r)
        (volume.restrict (auxCube 4 z)) ≤ ENNReal.ofReal B)
    (hCenters : ∀ z ∈ fixedLogGrid, |logGridMean w z - logGridMean w z₀| ≤ D) :
    eLpNorm (fun x => w x - logGridMean w z₀) (ENNReal.ofReal r)
        (volume.restrict (logOscillationDomain (d := d))) ≤
      ENNReal.ofReal (fixedLogGrid (d := d)).card * ENNReal.ofReal B +
        eLpNorm (fun _ : Vec d => D) (ENNReal.ofReal r)
          (volume.restrict (logOscillationDomain (d := d))) := by
  let S := logOscillationDomain (d := d)
  let μ := volume.restrict S
  let p := ENNReal.ofReal r
  have hSsub : S ⊆ originCube (d := d) 1 := by
    intro x hx i
    have hxi := hx i
    change -(7 / 8 / 2 : ℝ) < x i ∧ x i < 7 / 8 / 2 at hxi
    change -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2
    constructor <;> nlinarith
  have hSmeasure : μ ≤ volume.restrict (originCube (d := d) 1) := by
    dsimp [μ]
    exact Measure.restrict_mono_set volume hSsub
  have hwS : AEStronglyMeasurable w μ := hw.mono_measure hSmeasure
  let g : (Fin d → ℤ) → Vec d → ℝ := logGridDeviationOn w
  let gsum : Vec d → ℝ := fun x => ∑ z ∈ fixedLogGrid, g z x
  let f : Vec d → ℝ := fun x => w x - logGridMean w z₀
  have hSmeas : MeasurableSet S := by
    have hopen : IsOpen S := by
      change IsOpen {x : Vec d | ∀ i, (-(7 / 8 / 2 : ℝ)) < x i ∧ x i < 7 / 8 / 2}
      simp only [← Set.iInter_ofPred]
      exact isOpen_iInter_of_finite fun i =>
        isOpen_Ioo.preimage (continuous_apply i)
    exact hopen.measurableSet
  have hQmeas (z : Fin d → ℤ) : MeasurableSet (auxCube 4 z) :=
    Foundations.Reconstruction.measurableSet_auxCube 4 z
  have hcover : S ⊆ ⋃ z ∈ fixedLogGrid, auxCube 4 z := by
    intro x hx
    have hxClosed : x ∈ closedSevenEighthsCube := by
      intro i
      have hxi := hx i
      have hlo : -(7 / 16 : ℝ) < x i := by
        change -(7 / 8 / 2 : ℝ) < x i ∧ x i < 7 / 8 / 2 at hxi
        nlinarith [hxi.1]
      have hhi : x i < (7 / 16 : ℝ) := by
        change -(7 / 8 / 2 : ℝ) < x i ∧ x i < 7 / 8 / 2 at hxi
        nlinarith [hxi.2]
      exact abs_le.mpr ⟨le_of_lt hlo, le_of_lt hhi⟩
    exact fixedLogGrid_cover hxClosed
  have hpoint : ∀ x ∈ S, |f x| ≤ gsum x + D := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have hterm : g z x = |w x - logGridMean w z| := by
      simp [g, logGridDeviationOn, logGridDeviation, hxz]
    have hnonneg : ∀ z ∈ fixedLogGrid, 0 ≤ g z x := by
      intro z hz
      by_cases hxz' : x ∈ auxCube 4 z
      · simp [g, logGridDeviationOn, logGridDeviation, hxz']
      · simp [g, logGridDeviationOn, hxz']
    have hselected : g z x ≤ gsum x := by
      dsimp [gsum]
      exact Finset.single_le_sum (fun y hy => hnonneg y hy) hz
    have htri : |w x - logGridMean w z₀| ≤
        |w x - logGridMean w z| + |logGridMean w z - logGridMean w z₀| := by
      calc
        |w x - logGridMean w z₀| =
            |(w x - logGridMean w z) + (logGridMean w z - logGridMean w z₀)| := by
              congr 1
              ring
        _ ≤ |w x - logGridMean w z| +
            |logGridMean w z - logGridMean w z₀| := abs_add_le _ _
    calc
      |f x| = |w x - logGridMean w z₀| := rfl
      _ ≤ |w x - logGridMean w z| + D := by
        nlinarith [htri, hCenters z hz]
      _ = g z x + D := by rw [hterm]
      _ ≤ gsum x + D := by nlinarith [hselected]
  have hgsum_nonneg : ∀ x, 0 ≤ gsum x := by
    intro x
    dsimp [gsum]
    apply Finset.sum_nonneg
    intro z hz
    by_cases hxz : x ∈ auxCube 4 z <;>
      simp [g, logGridDeviationOn, logGridDeviation, hxz]
  have hmeasLocal (z : Fin d → ℤ) :
      AEStronglyMeasurable (g z) μ := by
    dsimp [g, logGridDeviationOn, μ]
    have hbase : AEStronglyMeasurable
        (fun x => |w x - logGridMean w z|) (volume.restrict S) :=
      (hwS.sub aestronglyMeasurable_const).norm
    exact hbase.indicator (hQmeas z)
  have hlocalRestrict (z : Fin d → ℤ) (hz : z ∈ fixedLogGrid) :
      eLpNorm (g z) p μ ≤ ENNReal.ofReal B := by
    change eLpNorm ((auxCube 4 z).indicator
      (fun x => |w x - logGridMean w z|)) p μ ≤ ENNReal.ofReal B
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (hQmeas z)]
    have hmeasure : (volume.restrict S).restrict (auxCube 4 z) ≤
        volume.restrict (auxCube 4 z) := by
      rw [Measure.restrict_restrict (hQmeas z)]
      exact volume.restrict_mono_set inter_subset_left
    have hmono := eLpNorm_mono_measure (p := p)
      (fun x => |w x - logGridMean w z|) hmeasure
    have hlocal := hLocal z hz
    have h15to1 : originCube (15 / 16 : ℝ) ⊆ originCube (d := d) 1 := by
      intro x hx i
      have hxi := hx i
      change -(15 / 16 / 2 : ℝ) < x i ∧ x i < 15 / 16 / 2 at hxi
      change -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2
      constructor <;> nlinarith
    have hQsub : auxCube 4 z ⊆ originCube (d := d) 1 :=
      (subset_closure.trans (fixedLogGrid_closure_inside hz)).trans h15to1
    have hQmeasure : volume.restrict (auxCube 4 z) ≤
        volume.restrict (originCube (d := d) 1) :=
      Measure.restrict_mono_set volume hQsub
    have hwQ : AEStronglyMeasurable w (volume.restrict (auxCube 4 z)) :=
      hw.mono_measure hQmeasure
    have hfQ : AEStronglyMeasurable
        (fun x => w x - logGridMean w z) (volume.restrict (auxCube 4 z)) :=
      hwQ.sub aestronglyMeasurable_const
    have hAbs : eLpNorm (fun x => |w x - logGridMean w z|) p
        (volume.restrict (auxCube 4 z)) =
        eLpNorm (fun x => w x - logGridMean w z) p
          (volume.restrict (auxCube 4 z)) := by
      apply eLpNorm_congr_norm_ae (hfQ.norm) hfQ
      filter_upwards with x
      simp only [Real.norm_eq_abs, abs_abs]
    have hlocal' : eLpNorm (fun x => |w x - logGridMean w z|) p
        (volume.restrict (auxCube 4 z)) ≤ ENNReal.ofReal B := by
      calc
        _ = eLpNorm (fun x => w x - logGridMean w z) p
            (volume.restrict (auxCube 4 z)) := hAbs
        _ = eLpNorm (fun x => w x - logGridMean w z) (ENNReal.ofReal r)
            (volume.restrict (auxCube 4 z)) := by simp [p]
        _ ≤ ENNReal.ofReal B := hlocal
    exact hmono.trans hlocal'
  have hsumBound : eLpNorm gsum p μ ≤
      ENNReal.ofReal (fixedLogGrid (d := d)).card * ENNReal.ofReal B := by
    have hsum := eLpNorm_sum_le_card_of_local_bounds p (ENNReal.ofReal B)
      (by simpa [p] using ENNReal.ofReal_le_ofReal hr) (fixedLogGrid (d := d))
      (fun z => g z) (fun z hz => hlocalRestrict z hz)
    simpa [p, ENNReal.ofReal_natCast] using hsum
  have hfinalMeas : AEStronglyMeasurable f μ := by
    dsimp [f, μ]
    exact hwS.sub aestronglyMeasurable_const
  have hpointAE : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖gsum x + D‖ := by
    filter_upwards [ae_restrict_mem hSmeas] with x hx
    have hxS : x ∈ S := hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (add_nonneg (hgsum_nonneg x) hD)]
    exact hpoint x hxS
  have hmono : eLpNorm f p μ ≤ eLpNorm (fun x => gsum x + D) p μ :=
    eLpNorm_mono_ae hfinalMeas hpointAE
  have hsumPlus : eLpNorm (fun x => gsum x + D) p μ ≤
      eLpNorm gsum p μ + eLpNorm (fun _ : Vec d => D) p μ := by
    exact eLpNorm_add_le (show 1 ≤ p by simpa [p] using ENNReal.ofReal_le_ofReal hr)
  have hsumPlusBound : eLpNorm gsum p μ + eLpNorm (fun _ : Vec d => D) p μ ≤
      ENNReal.ofReal (fixedLogGrid (d := d)).card * ENNReal.ofReal B +
        eLpNorm (fun _ : Vec d => D) p μ := by
    simpa [add_comm] using
      (add_le_add_left hsumBound (eLpNorm (fun _ : Vec d => D) p μ))
  exact hmono.trans (hsumPlus.trans hsumPlusBound)

end

end CoarseDeGiorgi.Harnack.Log
