module

public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxLipschitz
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Axial integration by parts without transverse regularity -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

def scalarAxialFluxFactor (d n : ℕ) (ζ δ r : ℝ) : ℝ :=
  scalarCylinderConductivity d n ζ r * scalarRadialProfile d n ζ r *
    scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ r

theorem scalarAxialFluxFactor_bound {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (δ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    |scalarAxialFluxFactor d n ζ δ r| ≤
      2 * (scalarCoreValue d n ζ (cylinderRadialConstant d) +
        scalarAnnulusValue d n ζ (cylinderRadialConstant d)) := by
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have hc : 0 ≤ scalarCoreValue d n ζ (cylinderRadialConstant d) :=
    mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hε.le _)
  have ha : 0 ≤ scalarAnnulusValue d n ζ (cylinderRadialConstant d) :=
    mul_nonneg (inv_nonneg.mpr (cylinderB_pos n).le) (Real.rpow_nonneg hε.le _)
  have hψ := scalarRadialProfile_bounds (n := n) hd hζ0 hζ2 hr
  have hχ := scalarOuterFluxCutoff_bounds (cylinderRadius d n ζ (cylinderRadialConstant d)) δ r
  have hb : scalarCylinderConductivity d n ζ r ≤
      scalarCoreValue d n ζ (cylinderRadialConstant d) +
        scalarAnnulusValue d n ζ (cylinderRadialConstant d) := by
    unfold scalarCylinderConductivity
    split_ifs
    · exact le_add_of_nonneg_right ha
    · exact le_add_of_nonneg_left hc
  unfold scalarAxialFluxFactor
  rw [abs_of_nonneg (mul_nonneg
    (mul_nonneg (scalarCylinderConductivity_pos hd hζ0 hζ2 r).le hψ.1) hχ.1)]
  exact (mul_le_mul (mul_le_mul hb hψ.2 hψ.1 (add_nonneg hc ha)) hχ.2 hχ.1
    (mul_nonneg (add_nonneg hc ha) (by norm_num))).trans_eq (by ring)

theorem scalarAxialFluxFactor_shifted_measurable {d : ℕ} (hd : 3 ≤ d)
    {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (δ : ℝ) :
    Measurable (fun x : Vec d => scalarAxialFluxFactor d n ζ δ
      (transverseNorm (x - cylinderCenter (cylinderB n)))) := by
  have hρ : Continuous (fun x : Vec d => transverseNorm (x - cylinderCenter (cylinderB n))) :=
    lineRadius_continuous.comp (continuous_id.sub continuous_const)
  have hA : Measurable (fun x : Vec d => scalarCylinderConductivity d n ζ
      (transverseNorm (x - cylinderCenter (cylinderB n)))) := by
    unfold scalarCylinderConductivity
    exact Measurable.ite (isOpen_lt hρ continuous_const).measurableSet measurable_const measurable_const
  obtain ⟨K, hC⟩ := scalarOuterFluxCutoff_exists_lipschitz
    (cylinderRadius d n ζ (cylinderRadialConstant d)) δ
  exact (hA.mul ((scalarRadialProfile_continuous (n := n) hd hζ0 hζ2).comp hρ).measurable).mul
    (hC.continuous.comp hρ).measurable

/-- A compactly supported test times the bounded radial factor and any
continuous axial factor is integrable on the whole space. -/
theorem scalarAxialFlux_test_integrable {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (δ : ℝ)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    {Y : ℝ → ℝ} (hY : Continuous Y) :
    Integrable (fun x => ψ x * scalarAxialFluxFactor d n ζ δ
      (transverseNorm (x - cylinderCenter (cylinderB n))) * Y (x 0)) volume := by
  have hi : Integrable (fun x : Vec d => ψ x * Y (x 0)) volume :=
    (hψ.mul (hY.comp (continuous_apply 0))).integrable_of_hasCompactSupport hc.mul_right
  have h := hi.mul_bdd
    (scalarAxialFluxFactor_shifted_measurable hd hζ0 hζ2 δ).aestronglyMeasurable
    (Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using scalarAxialFluxFactor_bound hd hζ0 hζ2 δ
        (lineRadius_nonneg (x - cylinderCenter (cylinderB n)))))
  convert h using 1
  funext x
  ring

/-- Axial integration by parts is unaffected by jumps in the transverse
conductivity, since the radial factors are constant on each axial line. -/
theorem integral_test_mul_scalarCutoffFlux_axial {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (δ : ℝ)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => fderiv ℝ φ x (basisVec (0 : Fin d)) * scalarCutoffFlux n ζ δ x 0) volume ∧
    Integrable (fun x => φ x * lineDeriv ℝ (fun y => scalarCutoffFlux n ζ δ y 0) x (basisVec (0 : Fin d))) volume ∧
    (∫ x, fderiv ℝ φ x (basisVec (0 : Fin d)) * scalarCutoffFlux n ζ δ x 0 ∂volume) =
      -(∫ x, φ x * lineDeriv ℝ (fun y => scalarCutoffFlux n ζ δ y 0) x (basisVec (0 : Fin d)) ∂volume) := by
  let A := fun x : Vec d => scalarAxialFluxFactor d n ζ δ
    (transverseNorm (x - cylinderCenter (cylinderB n)))
  let F := fun x : Vec d => scalarCutoffFlux n ζ δ x 0
  let D := fun x : Vec d => A x *
    (cylinderRate d n (cylinderRadialConstant d) ^ 2 * scalarAxialProfile d n ζ (x 0))
  have hX : Continuous (scalarAxialProfile d n ζ) :=
    continuous_iff_continuousAt.mpr (fun t => (scalarAxialProfile_hasDerivAt d n ζ t).continuousAt)
  have hX' : Continuous (scalarAxialDerivative d n ζ) :=
    continuous_iff_continuousAt.mpr (fun t => (scalarAxialDerivative_hasDerivAt d n ζ t).continuousAt)
  have hF (x : Vec d) : F x = A x * scalarAxialDerivative d n ζ (x 0) := by rfl
  have hD (x : Vec d) : HasLineDerivAt ℝ F (D x) x (basisVec (0 : Fin d)) :=
    scalarCutoffFlux_axial_hasLineDerivAt n ζ δ x
  have hiL : Integrable (fun x => fderiv ℝ φ x (basisVec (0 : Fin d)) * F x) volume := by
    simp_rw [hF]
    have h := scalarAxialFlux_test_integrable (n := n) hd hζ0 hζ2 δ
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply ℝ (basisVec (0 : Fin d))) hX'
    simpa only [A, mul_assoc] using h
  have hiR : Integrable (fun x => φ x * D x) volume := by
    have h := scalarAxialFlux_test_integrable (n := n)
      (Y := fun t => cylinderRate d n (cylinderRadialConstant d) ^ 2 * scalarAxialProfile d n ζ t)
      hd hζ0 hζ2 δ hφ.continuous hc (continuous_const.mul hX)
    simpa only [A, D, mul_assoc] using h
  have hiP : Integrable (fun x => φ x * F x) volume := by
    simp_rw [hF]
    have h := scalarAxialFlux_test_integrable (n := n) hd hζ0 hζ2 δ hφ.continuous hc hX'
    simpa only [A, mul_assoc] using h
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) hiL hiR hiP
    (fun x _ => (hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (basisVec (0 : Fin d)))
    (fun x _ => hD x)
  have heq : (fun x => lineDeriv ℝ F x (basisVec (0 : Fin d))) = D :=
    funext (fun x => (hD x).lineDeriv)
  refine ⟨hiL, ?_, ?_⟩
  · simpa only [← heq, F] using hiR
  · simpa only [← heq, F, ContinuousLinearMap.mul_apply'] using (neg_eq_iff_eq_neg.mp hibp.symm)

end

end CoarseDeGiorgi.SharpnessExamples
