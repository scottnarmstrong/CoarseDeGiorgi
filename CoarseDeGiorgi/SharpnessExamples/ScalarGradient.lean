import CoarseDeGiorgi.SharpnessExamples.ScalarMembership
import CoarseDeGiorgi.SharpnessExamples.ScalarNullSets

/-! # Classical gradients of the cylinder profiles off their null interfaces -/

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The radial derivative on the three open regions. Interface values are
irrelevant to the almost-everywhere gradient. -/
def scalarRadialDerivative (d n : ℕ) (ζ r : ℝ) : ℝ :=
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  if r < ε then -2 * scalarProfileXi d n ζ * r / ε ^ 2
  else if r < 2 * ε then -cylinderRadialConstant d / ε * Real.rpow (r / ε) (2 - (d : ℝ))
  else 0

theorem scalarRadialProfile_outer_hasDerivAt {d n : ℕ} {ζ r : ℝ}
    (hr0 : 0 < r)
    (hr : 2 * cylinderRadius d n ζ (cylinderRadialConstant d) < r) :
    HasDerivAt (scalarRadialProfile d n ζ) 0 r := by
  have heq : scalarRadialProfile d n ζ =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_gt_nhds hr, eventually_gt_nhds hr0] with t ht ht0
    unfold scalarRadialProfile
    rw [ite_eq_right (by linarith : ¬t ≤ cylinderRadius d n ζ (cylinderRadialConstant d)),
      ite_eq_right (not_lt.mpr ht.le)]
  exact (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq heq

theorem scalarRadialProfile_hasDerivAt {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hr : 0 < r)
    (hinner : r ≠ cylinderRadius d n ζ (cylinderRadialConstant d))
    (houter : r ≠ 2 * cylinderRadius d n ζ (cylinderRadialConstant d)) :
    HasDerivAt (scalarRadialProfile d n ζ) (scalarRadialDerivative d n ζ r) r := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  unfold scalarRadialDerivative
  change HasDerivAt (scalarRadialProfile d n ζ)
    (if r < ε then -2 * scalarProfileXi d n ζ * r / ε ^ 2
      else if r < 2 * ε then -cylinderRadialConstant d / ε * Real.rpow (r / ε) (2 - (d : ℝ))
      else 0) r
  by_cases h1 : r < ε
  · rw [ite_eq_left h1]
    exact
      scalarRadialProfile_core_hasDerivAt hr h1
  · have h1' : ε < r := lt_of_le_of_ne (le_of_not_gt h1) hinner.symm
    by_cases h2 : r < 2 * ε
    · rw [ite_eq_right h1, ite_eq_left h2]
      exact
        scalarRadialProfile_annulus_hasDerivAt hd hζ0 hζ2 h1' h2
    · rw [ite_eq_right h1, ite_eq_right h2]
      exact scalarRadialProfile_outer_hasDerivAt hr
        (lt_of_le_of_ne (le_of_not_gt h2) houter.symm)

/-- The source's gradient formula, with the axial and transverse components
kept separate. -/
def scalarCylinderGradient {d : ℕ} [NeZero d] (n : ℕ) (ζ : ℝ) (x : Vec d) : Vec d :=
  let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
  fun i => if i = 0 then scalarAxialDerivative d n ζ (x 0) * scalarRadialProfile d n ζ r
    else scalarAxialProfile d n ζ (x 0) * scalarRadialDerivative d n ζ r *
      ((x - cylinderCenter (d := d) (cylinderB n)) i / r)

theorem scalarCylinderSubsolution_gradient_eq {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) {x : Vec d}
    (hr : 0 < transverseNorm (x - cylinderCenter (cylinderB n)))
    (hinner : transverseNorm (x - cylinderCenter (cylinderB n)) ≠
      cylinderRadius d n ζ (cylinderRadialConstant d))
    (houter : transverseNorm (x - cylinderCenter (cylinderB n)) ≠
      2 * cylinderRadius d n ζ (cylinderRadialConstant d)) :
    smoothGrad (scalarCylinderSubsolution n ζ) x = scalarCylinderGradient n ζ x := by
  let c := cylinderCenter (d := d) (cylinderB n)
  let r := transverseNorm (x - c)
  have hψ := scalarRadialProfile_hasDerivAt hd hζ0 hζ2 hr hinner houter
  have hρbase : DifferentiableAt ℝ (transverseNorm (d := d)) (x - c) :=
    (transverseNorm_contDiffAt (x - c) hr).differentiableAt (by simp)
  have hρ : DifferentiableAt ℝ (fun y : Vec d => transverseNorm (y - c)) x :=
    DifferentiableAt.comp (g := transverseNorm) (f := fun y : Vec d => y - c)
      x hρbase (differentiableAt_id.sub_const c)
  have hX : DifferentiableAt ℝ (fun y : Vec d => scalarAxialProfile d n ζ (y 0)) x :=
    DifferentiableAt.comp (g := scalarAxialProfile d n ζ) (f := fun y : Vec d => y 0)
      x (scalarAxialProfile_hasDerivAt d n ζ (x 0)).differentiableAt
      ((ContinuousLinearMap.proj (0 : Fin d) : Vec d →L[ℝ] ℝ).differentiableAt)
  have hv : DifferentiableAt ℝ (scalarCylinderSubsolution n ζ) x :=
    hX.mul (DifferentiableAt.comp (g := scalarRadialProfile d n ζ)
      (f := fun y : Vec d => transverseNorm (y - c)) x hψ.differentiableAt hρ)
  ext i
  have hρline : HasDerivAt (fun t : ℝ => transverseNorm ((x + t • basisVec i) - c))
      (if i = 0 then (0 : ℝ) else (x - c) i / r) 0 := by
    have h := transverseNorm_hasDerivAt (x - c) i hr
    convert h using 1
    funext t
    congr 1
    abel
  have hXline := (scalarAxialProfile_hasDerivAt d n ζ (x 0)).comp_of_eq 0
    (axialCoordinatePath_hasDerivAt x i) (by simp)
  have hψline := hψ.comp_of_eq 0 hρline (by simp [c])
  have hvline := hXline.mul hψline
  change fderiv ℝ (scalarCylinderSubsolution n ζ) x (basisVec i) = _
  rw [fderiv_apply_eq_deriv_line hv i]
  have hvline' : HasDerivAt (fun t : ℝ => scalarCylinderSubsolution n ζ (x + t • basisVec i))
      (scalarAxialDerivative d n ζ (x 0) * (if i = 0 then 1 else 0) *
        scalarRadialProfile d n ζ r +
        scalarAxialProfile d n ζ (x 0) *
          (scalarRadialDerivative d n ζ r * (if i = 0 then 0 else (x - c) i / r))) 0 := by
    convert hvline using 1 <;>
      simp only [Function.comp_def, zero_smul, add_zero, c, r,
        scalarCylinderSubsolution]
    rfl
  rw [hvline'.deriv]
  by_cases hi : i = 0
  · simp only [scalarCylinderGradient, hi, ite_true, mul_zero, add_zero, mul_one, c, r]
  · simp only [scalarCylinderGradient, hi, ite_false, mul_zero, c, r]
    ring

/-- All cylinder interfaces and axes can be discarded simultaneously when
identifying the source's classical gradient. -/
theorem scalarCylinderSubsolution_gradient_ae {m : ℕ} (hm : 2 ≤ m)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    smoothGrad (scalarCylinderSubsolution (d := m + 1) n ζ) =ᵐ[volume]
      scalarCylinderGradient n ζ := by
  have hε := (cylinderRadius_data (d := m + 1) (n := n) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))).1
  filter_upwards [shifted_transverseNorm_pos_ae (by omega : 2 ≤ m + 1) (cylinderCenter (cylinderB n)),
    shifted_transverseNorm_ne_ae (cylinderCenter (cylinderB n)) hε.ne',
    shifted_transverseNorm_ne_ae (cylinderCenter (cylinderB n))
      (mul_pos (by norm_num : (0 : ℝ) < 2) hε).ne']
    with x hx h1 h2
  exact scalarCylinderSubsolution_gradient_eq (by omega) hζ0 hζ2 hx h1 h2

end

end CoarseDeGiorgi.SharpnessExamples
