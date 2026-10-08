import CoarseDeGiorgi.SharpnessExamples.ScalarFluxCalculus

/-! # Divergence of the matched flux, including the outer cutoff term -/

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- Summing the coordinate derivatives gives the radial divergence in the
exact transverse dimension `d-1`. -/
theorem scalarCutoffFlux_divergence_formula {d : ℕ} [NeZero d]
    {n : ℕ} {ζ δ : ℝ} {x : Vec d}
    (hr : 0 < transverseNorm (x - cylinderCenter (cylinderB n))) {H' C' : ℝ}
    (hH : HasDerivAt (scalarRadialFluxFactor d n ζ) H'
      (transverseNorm (x - cylinderCenter (cylinderB n))))
    (hC : HasDerivAt (scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ) C'
      (transverseNorm (x - cylinderCenter (cylinderB n)))) :
    let r := transverseNorm (x - cylinderCenter (cylinderB n))
    let H := scalarRadialFluxFactor d n ζ r
    let C := scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ r
    let X := scalarAxialProfile d n ζ (x 0)
    (∑ i : Fin d, lineDeriv ℝ (fun y => scalarCutoffFlux n ζ δ y i) x (basisVec i)) =
      scalarCylinderConductivity d n ζ r * scalarRadialProfile d n ζ r * C *
        (cylinderRate d n (cylinderRadialConstant d) ^ 2 * X) +
      X * (((d : ℝ) - 1) * H * C + (H' * C + H * C') * r) := by
  classical
  let y := x - cylinderCenter (d := d) (cylinderB n)
  let r := transverseNorm y
  let H := scalarRadialFluxFactor d n ζ r
  let C := scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ r
  let X := scalarAxialProfile d n ζ (x 0)
  let A := scalarCylinderConductivity d n ζ r * scalarRadialProfile d n ζ r * C *
    (cylinderRate d n (cylinderRadialConstant d) ^ 2 * X)
  have hsq : (∑ i : Fin d, if i = 0 then (0 : ℝ) else y i ^ 2) = r ^ 2 := by
    dsimp only [r]
    rw [transverseNorm, euclideanNorm_sq]
    unfold vecNormSq vecDot transversePart
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0
    · subst i
      simp
    · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp only [hi, hiv, ite_false, pow_two]
  have hcount : (∑ i : Fin d, if i = 0 then (0 : ℝ) else 1) = (d : ℝ) - 1 := by
    have heq : (∑ i : Fin d, if i = 0 then (0 : ℝ) else 1) =
        (∑ _i : Fin d, (1 : ℝ)) - (∑ i : Fin d, if i = 0 then (1 : ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> norm_num
    rw [heq]
    simp
  have hterm (i : Fin d) :
      lineDeriv ℝ (fun z => scalarCutoffFlux n ζ δ z i) x (basisVec i) =
      (if i = 0 then A else 0) + X * H * C * (if i = 0 then 0 else 1) +
        X * (H' * C + H * C') / r * (if i = 0 then 0 else y i ^ 2) := by
    by_cases hi : i = 0
    · subst i
      rw [(scalarCutoffFlux_axial_hasLineDerivAt n ζ δ x).lineDeriv]
      simp only [ite_true, mul_zero, add_zero, A, r, y, C, X]
    · rw [(scalarCutoffFlux_transverse_hasLineDerivAt hi hr hH hC).lineDeriv]
      simp only [ite_eq_right hi, zero_add, mul_one, X, H, C, r, y]
      ring
  dsimp only
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hsq, hcount]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  dsimp only [A, X, H, C, r, y]
  field_simp
  ring

end

end CoarseDeGiorgi.SharpnessExamples
