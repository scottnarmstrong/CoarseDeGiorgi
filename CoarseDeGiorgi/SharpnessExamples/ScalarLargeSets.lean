import CoarseDeGiorgi.SharpnessExamples.ScalarProfile
import CoarseDeGiorgi.Whitney.ExteriorCells
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Large values of the cylinder sum on sets of positive measure

The pointwise sum is finite at every point, since the closed outer cylinders
are disjoint. Its lower bound on each open core gives the large-set input of
`sharpness_range_of_scalar_subsolution`.
-/

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The pointwise sum of the source's cylinder profiles. -/
def scalarSubsolutionSum {d : ℕ} [NeZero d] (ζ : ℝ) (x : Vec d) : ℝ :=
  ∑' n : ℕ, scalarCylinderSubsolution n ζ x

theorem scalarCylinderSubsolution_support_outer {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    {n : ℕ} {x : Vec d} (hx : scalarCylinderSubsolution n ζ x ≠ 0) :
    x ∈ outerCylinder n ζ (cylinderRadialConstant d) := by
  have hr : transverseNorm (x - cylinderCenter (cylinderB n)) <
      2 * cylinderRadius d n ζ (cylinderRadialConstant d) := by
    by_contra h
    have hzero := scalarRadialProfile_eq_zero hd hζ0 hζ2 (le_of_not_gt h)
    exact hx (by simp only [scalarCylinderSubsolution, hzero, mul_zero])
  exact hr.le

/-- The sum agrees with the single profile throughout its open core. -/
theorem scalarSubsolutionSum_eq_on_core {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    {n : ℕ} {x : Vec d} (hx : x ∈ scalarCoreBand n ζ (cylinderRadialConstant d)) :
    scalarSubsolutionSum ζ x = scalarCylinderSubsolution n ζ x := by
  classical
  have hκ := cylinderRadialConstant_pos hd
  have hrad := (cylinderRadius_data hd hζ0 hζ2 hκ (d := d) (n := n)).1
  have hxn : x ∈ outerCylinder n ζ (cylinderRadialConstant d) := by
    change transverseNorm (x - cylinderCenter (cylinderB n)) ≤ _
    change transverseNorm (x - cylinderCenter (cylinderB n)) < _ at hx
    linarith
  apply tsum_eq_single
  intro j hjn
  by_contra hj
  have hxj := scalarCylinderSubsolution_support_outer hd hζ0 hζ2 hj
  rcases lt_or_gt_of_ne hjn with hlt | hgt
  · exact (Set.disjoint_left.mp (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hlt)) hxj hxn
  · exact (Set.disjoint_left.mp (outerCylinder_pairwise_disjoint hd hζ0 hζ2 hκ hgt)) hxn hxj

theorem scalarSubsolutionSum_nonneg {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (x : Vec d) :
    0 ≤ scalarSubsolutionSum ζ x :=
  tsum_nonneg (fun n => scalarCylinderSubsolution_nonneg hd hζ0 hζ2 n x)

/-- Each core meets the half cube in a nonempty open set of positive volume. -/
theorem scalarCore_halfCube_measure_pos {d : ℕ} (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    0 < volume (scalarCoreBand (d := d) n ζ (cylinderRadialConstant d) ∩ originCube (1 / 2)) := by
  have hrad := (cylinderRadius_data hd hζ0 hζ2 (cylinderRadialConstant_pos hd)
    (d := d) (n := n)).1
  have hc : IsOpen (scalarCoreBand (d := d) n ζ (cylinderRadialConstant d)) :=
    isOpen_lt (lineRadius_continuous.comp (continuous_id.sub continuous_const)) continuous_const
  have hV := CoarseDeGiorgi.Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1 / 2)
  apply (hc.inter hV.isOpen).measure_pos (μ := volume)
  refine ⟨cylinderCenter (cylinderB n), ?_, ?_⟩
  · simpa [scalarCoreBand, transverseNorm, transversePart, euclideanNorm, vecNormSq, vecDot] using hrad
  · intro i
    have hb := cylinderB_pos n
    have hbs := cylinderB_le_eighth n
    dsimp [originCube, CoarseDeGiorgi.originCube, cylinderCenter]
    split_ifs <;> constructor <;> linarith

/-- Exact large-set interface consumed by the range assembly. -/
theorem scalarSubsolutionSum_large_sets {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    ∀ N : ℕ, ∃ E : Set (Vec d),
      E ⊆ originCube (1 / 2) ∧ 0 < (volume.restrict E) Set.univ ∧
      ∀ᵐ x ∂(volume.restrict E), (N : ℝ) ≤ scalarSubsolutionSum ζ x := by
  intro N
  let n := 2 * N
  let E := scalarCoreBand (d := d) n ζ (cylinderRadialConstant d) ∩ originCube (1 / 2)
  have hE : MeasurableSet E :=
    (scalarCoreBand_measurable n ζ (cylinderRadialConstant d)).inter
      (CoarseDeGiorgi.Whitney.source_cube_domain (d := d) (by norm_num : (0 : ℝ) < 1 / 2)).isOpen.measurableSet
  refine ⟨E, Set.inter_subset_right, ?_, ?_⟩
  · simpa only [Measure.restrict_apply_univ] using scalarCore_halfCube_measure_pos hd hζ0 hζ2 n
  · filter_upwards [ae_restrict_mem hE] with x hx
    rw [scalarSubsolutionSum_eq_on_core hd hζ0 hζ2 hx.1]
    have hb := scalarCylinderSubsolution_core_lower hd hζ0 hζ2 hx.1
    have hheight : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 2 := by
      dsimp [n]
      push_cast
      linarith
    exact hheight.trans hb

end

end CoarseDeGiorgi.SharpnessExamples
