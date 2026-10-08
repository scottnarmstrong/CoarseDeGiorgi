import CoarseDeGiorgi.SharpnessExamples.ScalarFluxRegularity

/-! # Cutoff flux coordinates for the cylinder subsolution -/

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The single cylinder's conductivity, used only where its profile is nonzero.
The interface value is immaterial. -/
def scalarCylinderConductivity (d n : ℕ) (ζ r : ℝ) : ℝ :=
  if r < cylinderRadius d n ζ (cylinderRadialConstant d)
  then scalarCoreValue d n ζ (cylinderRadialConstant d)
  else scalarAnnulusValue d n ζ (cylinderRadialConstant d)

/-- The source flux with a decreasing cutoff at the outer interface. -/
def scalarCutoffFlux {d : ℕ} [NeZero d] (n : ℕ) (ζ δ : ℝ) (x : Vec d) : Vec d :=
  let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
  let χ := scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ r
  fun i => if i = 0 then
    scalarCylinderConductivity d n ζ r * scalarRadialProfile d n ζ r * χ *
      scalarAxialDerivative d n ζ (x 0)
  else scalarAxialProfile d n ζ (x 0) * scalarRadialFluxFactor d n ζ r * χ *
    (x - cylinderCenter (d := d) (cylinderB n)) i

theorem scalarCylinderConductivity_pos {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (r : ℝ) :
    0 < scalarCylinderConductivity d n ζ r := by
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  unfold scalarCylinderConductivity
  split_ifs
  · exact mul_pos (cylinderB_pos n) (Real.rpow_pos_of_pos hε _)
  · exact mul_pos (inv_pos.mpr (cylinderB_pos n)) (Real.rpow_pos_of_pos hε _)

theorem shifted_transverseNorm_axial_add {d : ℕ} [NeZero d]
    (x c : Vec d) (t : ℝ) :
    transverseNorm ((x + t • basisVec (0 : Fin d)) - c) = transverseNorm (x - c) := by
  have heq : transversePart ((x + t • basisVec (0 : Fin d)) - c) = transversePart (x - c) := by
    ext j
    by_cases hj : j = 0
    · subst j
      simp [transversePart]
    · have hjval : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [transversePart, hjval, basisVec, hj]
  change Foundations.Euclid.eNorm2 _ = Foundations.Euclid.eNorm2 _
  rw [heq]

/-- The axial coordinate has an ordinary derivative even at the transverse
interfaces: motion along the axis leaves every radial factor fixed. -/
theorem scalarCutoffFlux_axial_hasLineDerivAt {d : ℕ} [NeZero d] (n : ℕ) (ζ δ : ℝ)
    (x : Vec d) :
    HasLineDerivAt ℝ (fun y => scalarCutoffFlux n ζ δ y 0)
      (scalarCylinderConductivity d n ζ (transverseNorm (x - cylinderCenter (d := d) (cylinderB n))) *
        scalarRadialProfile d n ζ (transverseNorm (x - cylinderCenter (d := d) (cylinderB n))) *
        scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ
          (transverseNorm (x - cylinderCenter (d := d) (cylinderB n))) *
        (cylinderRate d n (cylinderRadialConstant d) ^ 2 * scalarAxialProfile d n ζ (x 0)))
      x (basisVec (0 : Fin d)) := by
  have hX := (scalarAxialDerivative_hasDerivAt d n ζ (x 0)).comp_of_eq 0
    (axialCoordinatePath_hasDerivAt x (0 : Fin d)) (by simp)
  let A := scalarCylinderConductivity d n ζ (transverseNorm (x - cylinderCenter (d := d) (cylinderB n))) *
    scalarRadialProfile d n ζ (transverseNorm (x - cylinderCenter (d := d) (cylinderB n))) *
    scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ
      (transverseNorm (x - cylinderCenter (d := d) (cylinderB n)))
  change HasDerivAt (fun t : ℝ => scalarCutoffFlux n ζ δ (x + t • basisVec (0 : Fin d)) 0) _ 0
  convert hX.const_mul A using 1 <;>
    simp only [scalarCutoffFlux, ite_true, shifted_transverseNorm_axial_add,
      Function.comp_def, A, mul_one]

end

end CoarseDeGiorgi.SharpnessExamples
