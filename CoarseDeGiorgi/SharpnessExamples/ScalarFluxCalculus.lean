import CoarseDeGiorgi.SharpnessExamples.ScalarFluxDefs

/-! # Coordinate derivatives of the cutoff flux -/

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Differentiating a radial vector field along a transverse coordinate. -/
theorem radial_coordinate_flux_hasLineDerivAt {d : ℕ} [NeZero d]
    {X P : ℝ → ℝ} {X' P' : ℝ} {x c : Vec d} {i : Fin d} (hi : i ≠ 0)
    (hr : 0 < transverseNorm (x - c))
    (hX : HasDerivAt X X' (x 0)) (hP : HasDerivAt P P' (transverseNorm (x - c))) :
    HasLineDerivAt ℝ (fun y : Vec d => X (y 0) * P (transverseNorm (y - c)) * (y - c) i)
      (X (x 0) * (P (transverseNorm (x - c)) + P' * (x - c) i ^ 2 / transverseNorm (x - c)))
      x (basisVec i) := by
  let r := transverseNorm (x - c)
  have hρ : HasDerivAt (fun t : ℝ => transverseNorm ((x + t • basisVec i) - c))
      ((x - c) i / r) 0 := by
    have h := transverseNorm_hasDerivAt (x - c) i hr
    rw [ite_eq_right hi] at h
    convert h using 1
    funext t
    congr 1
    abel
  have hXline := hX.comp_of_eq 0 (axialCoordinatePath_hasDerivAt x i) (by simp)
  have hPline := hP.comp_of_eq 0 hρ (by simp)
  have hYi : HasDerivAt (fun t : ℝ => ((x + t • basisVec i) - c) i) 1 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (x i - c i)).add (hasDerivAt_id (0 : ℝ))) using 1
    · funext t
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec, Pi.single_eq_same,
        mul_one, id_eq]
      ring
    · norm_num
  change HasDerivAt (fun t : ℝ => X ((x + t • basisVec i) 0) *
    P (transverseNorm ((x + t • basisVec i) - c)) * ((x + t • basisVec i) - c) i) _ 0
  convert (hXline.mul hPline).mul hYi using 1 <;>
    first | rfl | (simp only [hi, ite_false, zero_smul, add_zero, Function.comp_def,
      mul_zero, zero_mul, zero_add, mul_one, Pi.mul_apply, div_eq_mul_inv, r]; ring)

/-- The transverse derivative formula on either smooth radial branch. -/
theorem scalarCutoffFlux_transverse_hasLineDerivAt {d : ℕ} [NeZero d]
    {n : ℕ} {ζ δ : ℝ} {x : Vec d} {i : Fin d} (hi : i ≠ 0)
    (hr : 0 < transverseNorm (x - cylinderCenter (d := d) (cylinderB n)))
    {H' C' : ℝ}
    (hH : HasDerivAt (scalarRadialFluxFactor d n ζ) H'
      (transverseNorm (x - cylinderCenter (d := d) (cylinderB n))))
    (hC : HasDerivAt (scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ) C'
      (transverseNorm (x - cylinderCenter (d := d) (cylinderB n)))) :
    let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
    let H := scalarRadialFluxFactor d n ζ r
    let C := scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ r
    HasLineDerivAt ℝ (fun y => scalarCutoffFlux n ζ δ y i)
      (scalarAxialProfile d n ζ (x 0) *
        (H * C + (H' * C + H * C') * (x - cylinderCenter (d := d) (cylinderB n)) i ^ 2 / r))
      x (basisVec i) := by
  have h := radial_coordinate_flux_hasLineDerivAt hi hr
    (scalarAxialProfile_hasDerivAt d n ζ (x 0)) (hH.mul hC)
  convert h using 1
  · funext y
    simp only [scalarCutoffFlux, ite_eq_right hi, Pi.mul_apply]
    ring

end

end CoarseDeGiorgi.SharpnessExamples
