module

public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxDefs
public import CoarseDeGiorgi.SharpnessExamples.ScalarGradientBounds

/-! # Identification of the cutoff field with the weighted source gradient -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem matVecMul_scalar_identity {d : ℕ} (w : ℝ) (g : Vec d) :
    matVecMul (w • (1 : Mat d)) g = w • g := by
  rw [smul_matVecMul]
  congr 1
  ext i
  simp [matVecMul, Matrix.one_apply]

theorem scalarRadialFluxFactor_annulus_eq {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hr1 : cylinderRadius d n ζ (cylinderRadialConstant d) < r)
    (hr2 : r < 2 * cylinderRadius d n ζ (cylinderRadialConstant d)) :
    scalarRadialFluxFactor d n ζ r = scalarAnnulusValue d n ζ (cylinderRadialConstant d) *
      scalarRadialDerivative d n ζ r / r := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε : 0 < ε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have hr0 := hε.trans hr1
  have hratio : 1 ≤ r / ε := (le_div_iff₀ hε).2 (by simpa only [one_mul] using hr1.le)
  dsimp only [scalarRadialFluxFactor, scalarRadialDerivative]
  rw [max_eq_right hratio, ite_eq_right (not_lt.mpr hr1.le), ite_eq_left hr2]
  simp only [Real.rpow_eq_pow]
  rw [show 2 - (d : ℝ) = (1 - (d : ℝ)) + 1 by ring,
    Real.rpow_add_one (div_pos hr0 hε).ne']
  dsimp only [ε] at hε ⊢
  field_simp [hε.ne', hr0.ne']

theorem scalarCutoffFlux_eq_weightedGradient {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {n : ℕ} {ζ δ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hδ : 0 < δ) {x : Vec d}
    (hr : 0 < transverseNorm (x - cylinderCenter (cylinderB n)))
    (hi : transverseNorm (x - cylinderCenter (cylinderB n)) ≠
      cylinderRadius d n ζ (cylinderRadialConstant d)) :
    scalarCutoffFlux n ζ δ x =
      scalarOuterFluxCutoff (cylinderRadius d n ζ (cylinderRadialConstant d)) δ
        (transverseNorm (x - cylinderCenter (cylinderB n))) •
      matVecMul (scalarSharpnessCoefficient ζ (cylinderRadialConstant d) x)
        (scalarCylinderGradient n ζ x) := by
  let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  let C := scalarOuterFluxCutoff ε δ r
  have hε : 0 < ε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  rw [scalarSharpnessCoefficient, matVecMul_scalar_identity]
  by_cases hc : r < ε
  · dsimp only [r, ε] at hc
    have hcore : x ∈ scalarCoreBand n ζ (cylinderRadialConstant d) := hc
    rw [scalarSharpnessWeight_eq_core hd hζ0 hζ2 (cylinderRadialConstant_pos hd) hcore]
    have hH := scalarRadialFluxFactor_core hd hζ0 hζ2 hc.le
    ext i
    by_cases hi0 : i = 0
    · simp only [scalarCutoffFlux, scalarCylinderGradient, ite_eq_left hi0,
        scalarCylinderConductivity, ite_eq_left hc, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [scalarCutoffFlux, scalarCylinderGradient, ite_eq_right hi0,
        scalarRadialDerivative, ite_eq_left hc, Pi.smul_apply, smul_eq_mul]
      rw [hH]
      field_simp [hr.ne']
  · by_cases ha : r < 2 * ε
    · dsimp only [r, ε] at hc ha
      have hann : x ∈ scalarAnnulusBand n ζ (cylinderRadialConstant d) :=
        ⟨lt_of_le_of_ne (le_of_not_gt hc) hi.symm, ha⟩
      rw [scalarSharpnessWeight_eq_annulus hd hζ0 hζ2 (cylinderRadialConstant_pos hd) hann]
      have hH := scalarRadialFluxFactor_annulus_eq hd hζ0 hζ2 hann.1 hann.2
      ext i
      by_cases hi0 : i = 0
      · simp only [scalarCutoffFlux, scalarCylinderGradient, ite_eq_left hi0,
          scalarCylinderConductivity, ite_eq_right hc, Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [scalarCutoffFlux, scalarCylinderGradient, ite_eq_right hi0,
          Pi.smul_apply, smul_eq_mul]
        rw [hH]
        ring
    · have hzero := scalarOuterFluxCutoff_eq_zero hδ (le_of_not_gt ha)
      dsimp only [ε, r] at hzero
      rw [hzero, zero_smul]
      ext i
      simp only [scalarCutoffFlux, hzero, mul_zero, zero_mul, ite_self, Pi.zero_apply]

theorem scalarCutoffFlux_eq_weightedGradient_ae {m : ℕ} (hm : 2 ≤ m)
    {n : ℕ} {ζ δ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hδ : 0 < δ) :
    scalarCutoffFlux (d := m + 1) n ζ δ =ᵐ[volume]
      fun x => scalarOuterFluxCutoff (cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))) δ
        (transverseNorm (x - cylinderCenter (cylinderB n))) •
      matVecMul (scalarSharpnessCoefficient ζ (cylinderRadialConstant (m + 1)) x)
        (scalarCylinderGradient n ζ x) := by
  have hε := (cylinderRadius_data (d := m + 1) (n := n) (by omega) hζ0 hζ2
    (cylinderRadialConstant_pos (d := m + 1) (by omega))).1
  filter_upwards [shifted_transverseNorm_pos_ae (by omega : 2 ≤ m + 1) (cylinderCenter (cylinderB n)),
    shifted_transverseNorm_ne_ae (cylinderCenter (cylinderB n)) hε.ne'] with x hr hi
  exact scalarCutoffFlux_eq_weightedGradient (by omega) hζ0 hζ2 hδ hr hi

end

end CoarseDeGiorgi.SharpnessExamples
