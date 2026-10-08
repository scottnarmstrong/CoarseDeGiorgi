module

public import CoarseDeGiorgi.Assembly.ClassicalMomentsPartition
public import CoarseDeGiorgi.Foundations.FracGeometry.FlatCoordinates
public import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open Homogenization MeasureTheory
open CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

/-- The open cylinder inside the unit cube, parallel to the first axis. -/
def averagesCylinder {n : ℕ} (epsilon : ℝ) (center : Vec n) : Set (Vec (n + 1)) :=
  originCube 1 ∩ {x | Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon}

/-- The fraction of a set occupied by the cylinder, written as a normalized
average. For a simplex cell this is the geometric fraction in
Lemma `l.sharpness.cylinder.averages`. -/
noncomputable def cylinderFraction {n : ℕ} (V : Set (Vec (n + 1)))
    (epsilon : ℝ) (center : Vec n) : ℝ :=
  volumeAverage V
    ({x | Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon}.indicator
      (fun _ => (1 : ℝ)))

/-- The scale profile `ε^n max {ε, 3^{-k}}^{-n(1-1/v)}` of the cylinder averages, as on the right
of `e.sharpness.cylinder.scales` (with `n = d - 1`). -/
noncomputable def cylinderPhi (n : ℕ) (v epsilon : ℝ) (k : ℕ) : ℝ :=
  Real.rpow epsilon (n : ℝ) *
    Real.rpow (max epsilon ((3 : ℝ) ^ (-(k : ℤ))))
      (-((n : ℝ) * (1 - 1 / v)))

theorem cylinderTube_measurable {n : ℕ} (epsilon : ℝ) (center : Vec n) :
    MeasurableSet
      {x : Vec (n + 1) | Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon} := by
  have hcont : Continuous (fun x : Vec (n + 1) =>
      Sharpness.transverseNorm (flatJoin 0 center - x)) :=
    Sharpness.lineRadius_continuous.comp (continuous_const.sub continuous_id)
  exact (isOpen_lt hcont continuous_const).measurableSet

theorem cylinderFraction_eq_measure_ratio {d : ℕ} (V : Set (Vec d))
    (E : Set (Vec d)) (hE : MeasurableSet E) :
    volumeAverage V (E.indicator (fun _ => (1 : ℝ))) =
      (volume (V ∩ E)).toReal / (volume V).toReal := by
  unfold Homogenization.volumeAverage
  rw [integral_indicator hE]
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [Measure.restrict_apply_univ, Measure.restrict_apply hE]
  rw [Set.inter_comm]
  ring

/-- On a triangulation cell the normalized average is exactly the source's
volume fraction of `averagesCylinder`. -/
theorem simplexCell_cylinderFraction_eq_source {n k : ℕ}
    (epsilon : ℝ) (center : Vec n) (eta : SimplexIndex (n + 1) k) :
    cylinderFraction (simplexCell k eta) epsilon center =
      (volume (simplexCell k eta ∩ averagesCylinder epsilon center)).toReal /
        (volume (simplexCell k eta)).toReal := by
  have hsets : simplexCell k eta ∩
      {x : Vec (n + 1) |
        Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon} =
      simplexCell k eta ∩ averagesCylinder epsilon center := by
    rw [averagesCylinder]
    ext x
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨hx, ht⟩
      exact ⟨hx, ⟨CoarseDeGiorgi.simplexCell_subset_originCube k eta hx, ht⟩⟩
    · rintro ⟨hx, ⟨_, ht⟩⟩
      exact ⟨hx, ht⟩
  calc
    _ = volumeAverage (simplexCell k eta)
        ({x : Vec (n + 1) |
          Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon}.indicator
          (fun _ => (1 : ℝ))) := rfl
    _ = (volume (simplexCell k eta ∩
        {x : Vec (n + 1) |
          Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon})).toReal /
        (volume (simplexCell k eta)).toReal :=
      cylinderFraction_eq_measure_ratio _ _ (cylinderTube_measurable epsilon center)
    _ = _ := by rw [hsets]

/-- The average of the source fractions over a level is exactly the volume of
the cylinder; the unit cube has volume one. -/
theorem cylinderFraction_level_sum {n : ℕ} (k : ℕ) (epsilon : ℝ)
    (center : Vec n) :
    ((triangulation (d := n + 1) k).attach.sum fun eta =>
      cylinderFraction (simplexCell k eta) epsilon center) /
        ((triangulation (d := n + 1) k).card : ℝ) =
      (volume (averagesCylinder epsilon center)).toReal := by
  classical
  have hfinite : volume (originCube (d := n + 1) 1) ≠ ⊤ := by
    rw [CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.originCube_volume_one]
    simp
  have hconstOn : IntegrableOn (fun _ : Vec (n + 1) => (1 : ℝ))
      (originCube 1) volume := integrableOn_const hfinite
  have hconst : Integrable (fun _ : Vec (n + 1) => (1 : ℝ))
      (volume.restrict (originCube 1)) := hconstOn
  have hE : IntegrableOn
      ({x : Vec (n + 1) | Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon}.indicator
        (fun _ => (1 : ℝ))) (originCube 1) volume := by
    change Integrable _ (volume.restrict (originCube 1))
    exact hconst.indicator (cylinderTube_measurable epsilon center)
  have hpart := CoarseDeGiorgi.Assembly.ClassicalMomentsImpl.partition_average k hE
  have hcube : (∫ x in originCube 1,
      ({x : Vec (n + 1) | Sharpness.transverseNorm (flatJoin 0 center - x) < epsilon}.indicator
        (fun _ => (1 : ℝ)) x)) = (volume (averagesCylinder epsilon center)).toReal := by
    rw [integral_indicator (cylinderTube_measurable epsilon center)]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
    rw [Measure.restrict_apply_univ,
      Measure.restrict_apply (cylinderTube_measurable epsilon center)]
    simp [averagesCylinder, Set.inter_comm]
  rw [hcube] at hpart
  simpa [cylinderFraction] using hpart

end CoarseDeGiorgi.SharpnessExamples
