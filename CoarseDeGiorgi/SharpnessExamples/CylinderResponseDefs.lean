import CoarseDeGiorgi.Sharpness.LineEquation.AxisGeometry
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Weighted.ResponseBoundsLower
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The anisotropic cylinder coefficient

The coefficient equals
diag(A, b, ..., b) where |y| < 2ε, and equals the identity elsewhere. We use
the same cylindrical extension on all of Euclidean space; its restriction to
the unit cube has the form of the field `e.sharpness.polynomial.field`.
-/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The open tube of radius 2ε around the first coordinate axis. -/
def responseCylinder {d : ℕ} (epsilon : ℝ) : Set (Vec d) :=
  {x | Sharpness.transverseNorm x < 2 * epsilon}

/-- The diagonal conductivity inside the tube. -/
def cylinderDiagonal {d : ℕ} (parallel perpendicular : ℝ) : Mat d :=
  Matrix.diagonal (fun i => if i.val = 0 then parallel else perpendicular)

/-- The cylindrical extension of the anisotropic cylinder coefficient. -/
def cylinderCoefficient {d : ℕ} (epsilon parallel perpendicular : ℝ) : CoeffField d :=
  by
    classical
    exact fun x => if x ∈ responseCylinder epsilon then
    cylinderDiagonal parallel perpendicular else 1

/-- The fraction of a domain occupied by the tube, expressed as an average. -/
def cylinderResponseFraction {d : ℕ} (V : Set (Vec d)) (epsilon : ℝ) : ℝ :=
  volumeAverage V ((responseCylinder epsilon).indicator (fun _ => (1 : ℝ)))

theorem responseCylinder_measurable {d : ℕ} (epsilon : ℝ) :
    MeasurableSet (responseCylinder (d := d) epsilon) :=
  (isOpen_lt Sharpness.lineRadius_continuous continuous_const).measurableSet

theorem cylinderDiagonal_posDef {d : ℕ} {parallel perpendicular : ℝ}
    (hp : 0 < parallel) (ht : 0 < perpendicular) :
    (cylinderDiagonal (d := d) parallel perpendicular).PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  split_ifs <;> assumption

theorem cylinderDiagonal_inv {d : ℕ} {parallel perpendicular : ℝ}
    (hp : parallel ≠ 0) (ht : perpendicular ≠ 0) :
    (cylinderDiagonal (d := d) parallel perpendicular)⁻¹ =
      cylinderDiagonal parallel⁻¹ perpendicular⁻¹ := by
  let v : Fin d → ℝ := fun i => if i.val = 0 then parallel else perpendicular
  have hvunit : IsUnit v := by
    rw [Pi.isUnit_iff]
    intro i
    dsimp [v]
    split_ifs <;> exact isUnit_iff_ne_zero.mpr (by assumption)
  let : Invertible v := hvunit.invertible
  have hvInv : (⅟v : Fin d → ℝ) = fun i => (v i)⁻¹ := by
    apply invOf_eq_right_inv
    ext i
    dsimp [v]
    split_ifs <;> simp [hp, ht]
  rw [cylinderDiagonal, Matrix.inv_diagonal]
  congr 1
  funext i
  change (Ring.inverse v) i = _
  rw [Ring.inverse_invertible v, hvInv]
  dsimp [v]
  split_ifs <;> rfl

theorem cylinderCoefficient_inv {d : ℕ} (epsilon : ℝ) {parallel perpendicular : ℝ}
    (hp : parallel ≠ 0) (ht : perpendicular ≠ 0) (x : Vec d) :
    (cylinderCoefficient epsilon parallel perpendicular x)⁻¹ =
      cylinderCoefficient epsilon parallel⁻¹ perpendicular⁻¹ x := by
  classical
  unfold cylinderCoefficient
  split_ifs
  · exact cylinderDiagonal_inv hp ht
  · simp

theorem cylinderCoefficient_weightedCoeffOn {d : ℕ} {V : Set (Vec d)}
    (hV : volume V ≠ ⊤) (epsilon : ℝ) {parallel perpendicular : ℝ}
    (hp : 0 < parallel) (ht : 0 < perpendicular) :
    IsWeightedCoeffOn V (cylinderCoefficient (d := d) epsilon parallel perpendicular) := by
  classical
  have hm : Measurable (cylinderCoefficient (d := d) epsilon parallel perpendicular) := by
    classical
    exact Measurable.ite (responseCylinder_measurable epsilon) measurable_const measurable_const
  refine ⟨hm.aestronglyMeasurable, ae_of_all _ (fun x => ?_), ?_, ?_⟩
  · unfold cylinderCoefficient
    split_ifs
    · exact cylinderDiagonal_posDef hp ht
    · exact Matrix.PosDef.one
  · have hi : Integrable (fun _ : Vec d =>
        (cylinderDiagonal (d := d) parallel perpendicular).trace) (volume.restrict V) :=
      integrableOn_const hV
    have ho : Integrable (fun _ : Vec d => (1 : Mat d).trace) (volume.restrict V) :=
      integrableOn_const hV
    have heq : (fun x : Vec d => (cylinderCoefficient epsilon parallel perpendicular x).trace) =
        (responseCylinder epsilon).piecewise
          (fun _ => (cylinderDiagonal (d := d) parallel perpendicular).trace)
          (fun _ => (1 : Mat d).trace) := by
      funext x
      dsimp [cylinderCoefficient, Set.piecewise]
      split_ifs <;> rfl
    rw [heq]
    exact Integrable.piecewise (responseCylinder_measurable epsilon)
      hi.integrableOn ho.integrableOn
  · simp_rw [cylinderCoefficient_inv epsilon hp.ne' ht.ne']
    have hi : Integrable (fun _ : Vec d =>
        (cylinderDiagonal (d := d) parallel⁻¹ perpendicular⁻¹).trace) (volume.restrict V) :=
      integrableOn_const hV
    have ho : Integrable (fun _ : Vec d => (1 : Mat d).trace) (volume.restrict V) :=
      integrableOn_const hV
    have heq : (fun x : Vec d => (cylinderCoefficient epsilon parallel⁻¹ perpendicular⁻¹ x).trace) =
        (responseCylinder epsilon).piecewise
          (fun _ => (cylinderDiagonal (d := d) parallel⁻¹ perpendicular⁻¹).trace)
          (fun _ => (1 : Mat d).trace) := by
      funext x
      dsimp [cylinderCoefficient, Set.piecewise]
      split_ifs <;> rfl
    rw [heq]
    exact Integrable.piecewise (responseCylinder_measurable epsilon)
      hi.integrableOn ho.integrableOn

/-- The average definition is the geometric volume fraction. -/
theorem cylinderResponseFraction_eq_volume {d : ℕ} (V : Set (Vec d)) (epsilon : ℝ) :
    cylinderResponseFraction V epsilon =
      (volume (V ∩ responseCylinder epsilon)).toReal / (volume V).toReal := by
  unfold cylinderResponseFraction volumeAverage
  rw [integral_indicator (responseCylinder_measurable epsilon)]
  simp only [integral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [Measure.restrict_apply_univ, Measure.restrict_apply (responseCylinder_measurable epsilon)]
  rw [Set.inter_comm]
  ring

end

end CoarseDeGiorgi.SharpnessExamples
