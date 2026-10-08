import CoarseDeGiorgi.SharpnessExamples.ScalarFluxDivergence

/-! # The nonnegative divergence of each cutoff cylinder flux -/

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The cutoff adds a nonnegative annular divergence term. The inner flux is
matched and the core divergence is a nonnegative multiple of `ψ-1`. -/
theorem scalarCutoffFlux_divergence_nonneg {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {n : ℕ} {ζ δ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hδ0 : 0 < δ)
    (hδε : δ < cylinderRadius d n ζ (cylinderRadialConstant d)) {x : Vec d}
    (hr : 0 < transverseNorm (x - cylinderCenter (cylinderB n)))
    (hi : transverseNorm (x - cylinderCenter (cylinderB n)) ≠
      cylinderRadius d n ζ (cylinderRadialConstant d))
    (hc : transverseNorm (x - cylinderCenter (cylinderB n)) ≠
      2 * cylinderRadius d n ζ (cylinderRadialConstant d) - δ)
    (ho : transverseNorm (x - cylinderCenter (cylinderB n)) ≠
      2 * cylinderRadius d n ζ (cylinderRadialConstant d)) :
    0 ≤ ∑ i : Fin d, lineDeriv ℝ (fun y => scalarCutoffFlux n ζ δ y i) x (basisVec i) := by
  let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  let H := scalarRadialFluxFactor d n ζ r
  let C := scalarOuterFluxCutoff ε δ r
  let C' := if 2 * ε - δ < r ∧ r < 2 * ε then -δ⁻¹ else 0
  let X := scalarAxialProfile d n ζ (x 0)
  let ψ := scalarRadialProfile d n ζ r
  let R := cylinderRate d n (cylinderRadialConstant d)
  have hX : 0 ≤ X := by
    have hl := scalarAxialProfile_lower (n := n) hd hζ0 hζ2 (x 0)
    exact (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / 2).trans hl
  have hψ : 0 ≤ ψ := (scalarRadialProfile_bounds hd hζ0 hζ2 hr.le).1
  have hC0 : 0 ≤ C := (scalarOuterFluxCutoff_bounds ε δ r).1
  have hC' : C' ≤ 0 := by
    dsimp only [C']
    split_ifs
    · exact neg_nonpos.mpr (inv_nonneg.mpr hδ0.le)
    · exact le_rfl
  have hH0 : H ≤ 0 := scalarRadialFluxFactor_nonpos hd hζ0 hζ2 r
  have hCder : HasDerivAt (scalarOuterFluxCutoff ε δ) C' r :=
    scalarOuterFluxCutoff_hasDerivAt hδ0 hc ho
  by_cases hcore : r < ε
  · have hHder := scalarRadialFluxFactor_hasDerivAt_core hd hζ0 hζ2 hcore
    rw [scalarCutoffFlux_divergence_formula hr hHder hCder]
    have hbefore : r < 2 * ε - δ := by linarith only [hcore, hδε]
    have hCone : C = 1 := scalarOuterFluxCutoff_eq_one hδ0 hbefore.le
    have hCzero : C' = 0 := ite_eq_right (fun h => (not_lt.mpr hbefore.le) h.1)
    have hcond : scalarCylinderConductivity d n ζ r = scalarCoreValue d n ζ (cylinderRadialConstant d) :=
      ite_eq_left hcore
    have hHval : H = scalarCoreValue d n ζ (cylinderRadialConstant d) *
        (-2 * scalarProfileXi d n ζ / ε ^ 2) :=
      scalarRadialFluxFactor_core hd hζ0 hζ2 hcore.le
    have hcancel : ((d : ℝ) - 1) * H = -scalarCoreValue d n ζ (cylinderRadialConstant d) * R ^ 2 := by
      have hcurv := scalarCore_curvature_eq_rate (n := n) hd hζ0 hζ2
      rw [hHval, ← hcurv]
      dsimp only [ε]
      ring
    have hψ1 : 1 ≤ ψ := (scalarRadialProfile_core_bounds hd hζ0 hζ2 hr.le hcore.le).1
    change 0 ≤ scalarCylinderConductivity d n ζ r * ψ * C * (R ^ 2 * X) +
      X * (((d : ℝ) - 1) * H * C + (0 * C + H * C') * r)
    rw [hCone, hCzero, hcond]
    simp only [mul_one, zero_mul, mul_zero, add_zero]
    rw [hcancel]
    have heq : scalarCoreValue d n ζ (cylinderRadialConstant d) * ψ * (R ^ 2 * X) +
        X * (-scalarCoreValue d n ζ (cylinderRadialConstant d) * R ^ 2) =
        scalarCoreValue d n ζ (cylinderRadialConstant d) * R ^ 2 * X * (ψ - 1) := by ring
    rw [heq]
    have ha : 0 ≤ scalarCoreValue d n ζ (cylinderRadialConstant d) := by
      rw [← hcond]
      exact (scalarCylinderConductivity_pos hd hζ0 hζ2 r).le
    exact mul_nonneg (mul_nonneg (mul_nonneg ha (sq_nonneg R)) hX) (sub_nonneg.mpr hψ1)
  · have hann : ε < r := lt_of_le_of_ne (le_of_not_gt hcore) hi.symm
    have hHder := scalarRadialFluxFactor_hasDerivAt_annulus hd hζ0 hζ2 hann
    rw [scalarCutoffFlux_divergence_formula hr hHder hCder]
    change 0 ≤ scalarCylinderConductivity d n ζ r * ψ * C * (R ^ 2 * X) +
      X * (((d : ℝ) - 1) * H * C + (H * (1 - (d : ℝ)) / r * C + H * C') * r)
    have heq : ((d : ℝ) - 1) * H * C + (H * (1 - (d : ℝ)) / r * C + H * C') * r = H * C' * r := by
      field_simp [show r ≠ 0 from hr.ne']
      ring
    rw [heq]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg
        (scalarCylinderConductivity_pos hd hζ0 hζ2 r).le hψ) hC0)
        (mul_nonneg (sq_nonneg R) hX))
      (mul_nonneg hX (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hH0 hC') hr.le))

/-- All exceptional spheres and the axis are null sets. -/
theorem scalarCutoffFlux_divergence_nonneg_ae {m : ℕ} (hm : 2 ≤ m)
    {n : ℕ} {ζ δ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hδ0 : 0 < δ)
    (hδε : δ < cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))) :
    ∀ᵐ x : Vec (m + 1) ∂volume,
      0 ≤ ∑ i : Fin (m + 1), lineDeriv ℝ (fun y => scalarCutoffFlux n ζ δ y i) x (basisVec i) := by
  let c := cylinderCenter (d := m + 1) (cylinderB n)
  let ε := cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))
  have hε : 0 < ε := (cylinderRadius_data (d := m + 1) (n := n) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (by omega))).1
  have hcut : 0 < 2 * ε - δ := by linarith only [hε, hδε]
  filter_upwards [shifted_transverseNorm_pos_ae (by omega : 2 ≤ m + 1) c,
    shifted_transverseNorm_ne_ae c hε.ne', shifted_transverseNorm_ne_ae c hcut.ne',
    shifted_transverseNorm_ne_ae c (mul_pos (by norm_num : (0 : ℝ) < 2) hε).ne'] with x hr hi hc ho
  exact scalarCutoffFlux_divergence_nonneg (by omega) hζ0 hζ2 hδ0 hδε hr hi hc ho

end

end CoarseDeGiorgi.SharpnessExamples
