module

public import CoarseDeGiorgi.SharpnessExamples.CylinderResponseAverages
public import CoarseDeGiorgi.SharpnessExamples.CylinderAveragesGeometry

/-! # Comparing the response cylinder with the cylinder-average geometry -/

@[expose] public section

open Homogenization MeasureTheory
open CoarseDeGiorgi.Foundations.FracGeometry
open scoped BigOperators Classical

namespace CoarseDeGiorgi.SharpnessExamples

/-- Transverse distance is unchanged by negating all coordinates. -/
theorem transverseNorm_neg {d : ℕ} (x : Vec d) :
    Sharpness.transverseNorm (-x) = Sharpness.transverseNorm x := by
  have h : Sharpness.transversePart (-x) = (-1 : ℝ) • Sharpness.transversePart x := by
    funext i
    simp [Sharpness.transversePart]
  change Foundations.Euclid.eNorm2 (Sharpness.transversePart (-x)) = _
  rw [h, Foundations.Euclid.eNorm2_smul]
  simp [Sharpness.transverseNorm, euclideanNorm, Foundations.Euclid.eNorm2]

/-- The response fraction uses the radius 2ε and zero center in
Lemma `l.sharpness.cylinder.averages`. -/
theorem cylinderResponseFraction_eq_cylinderFraction {n : ℕ}
    (V : Set (Vec (n + 1))) (epsilon : ℝ) :
    cylinderResponseFraction V epsilon = cylinderFraction V (2 * epsilon) 0 := by
  unfold cylinderResponseFraction cylinderFraction responseCylinder
  congr 1
  have hzero : flatJoin (n := n) 0 (0 : Vec n) = 0 := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [hzero, zero_sub, transverseNorm_neg]

end CoarseDeGiorgi.SharpnessExamples
