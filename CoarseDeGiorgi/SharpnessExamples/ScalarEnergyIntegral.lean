module

public import CoarseDeGiorgi.SharpnessExamples.ScalarEnergyPointwise

/-! # Summable weighted value and energy of the cylinder profiles -/

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem indicator_lintegral_cube {d : ℕ} (E : Set (Vec d))
    (hE : MeasurableSet E) (C : ℝ) :
    (∫⁻ x in originCube 1, E.indicator (fun _ => ENNReal.ofReal C) x ∂volume) =
      ENNReal.ofReal (C * (volume (E ∩ originCube 1)).toReal) := by
  have htop : volume (E ∩ originCube (d := d) 1) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (by rw [Assembly.ClassicalMomentsImpl.originCube_volume_one]; simp)
      (measure_mono Set.inter_subset_right)
  rw [lintegral_indicator_const hE, Measure.restrict_apply hE]
  conv_lhs => arg 2; rw [← ENNReal.ofReal_toReal htop]
  exact (ENNReal.ofReal_mul' ENNReal.toReal_nonneg).symm

/-- The literal source cylinder profiles have summable weighted value and
gradient squares. The constant depends only on the ambient dimension. -/
theorem scalarCylinder_value_energy_bound {m : ℕ} (hm : 2 ≤ m) {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (n : ℕ) :
    (∫⁻ x : Vec (m + 1) in originCube 1, ENNReal.ofReal
      (scalarSharpnessWeight ζ (cylinderRadialConstant (m + 1)) x *
        (scalarCylinderSubsolution n ζ x ^ 2 +
          vecNormSq (scalarCylinderGradient n ζ x))) ∂volume) ≤
      ENNReal.ofReal (2 * (4 : ℝ) ^ m * scalarEnergyConstant (m + 1) * (1 / 2 : ℝ) ^ (n + 1)) := by
  classical
  let d := m + 1
  let κ := cylinderRadialConstant d
  let ε := cylinderRadius d n ζ κ
  let R := cylinderRate d n κ
  let M := ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp R
  let T := (cylinderB n)⁻¹ * Real.rpow ε (cylinderNu d ζ)
  let Kc := 4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (2 * scalarProfileXi d n ζ / ε) ^ 2
  let Ka := 4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (κ / ε) ^ 2
  let Cc := Kc * scalarCoreValue d n ζ κ * M
  let Ca := Ka * scalarAnnulusValue d n ζ κ * M
  let Ec := scalarCoreBand (d := d) n ζ κ
  let Ea := scalarAnnulusBand (d := d) n ζ κ
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hκ : 0 < κ := cylinderRadialConstant_pos hd
  have hdata := cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2 hκ
  have hε : 0 < ε := hdata.1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hCc : 0 ≤ Cc := by
    dsimp [Cc, Kc, scalarCoreValue]
    exact mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hε.le _))) hM
  have hCa : 0 ≤ Ca := by
    dsimp [Ca, Ka, scalarAnnulusValue]
    exact mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg (inv_nonneg.mpr (cylinderB_pos n).le) (Real.rpow_nonneg hε.le _))) hM
  have hEC : MeasurableSet Ec := scalarCoreBand_measurable n ζ κ
  have hEA : MeasurableSet Ea := scalarAnnulusBand_measurable n ζ κ
  have hmajor : ∀ᵐ x ∂volume.restrict (originCube (d := d) 1),
      ENNReal.ofReal (scalarSharpnessWeight ζ κ x *
        (scalarCylinderSubsolution n ζ x ^ 2 + vecNormSq (scalarCylinderGradient n ζ x))) ≤
      Ec.indicator (fun _ => ENNReal.ofReal Cc) x + Ea.indicator (fun _ => ENNReal.ofReal Ca) x := by
    have haxis := ae_restrict_of_ae (s := originCube (d := d) 1)
      (shifted_transverseNorm_pos_ae (by omega : 2 ≤ d) (cylinderCenter (cylinderB n)))
    have hinter := ae_restrict_of_ae (s := originCube (d := d) 1)
      (shifted_transverseNorm_ne_ae (cylinderCenter (d := d) (cylinderB n)) hε.ne')
    filter_upwards [ae_restrict_mem (Whitney.source_cube_domain (d := d) (by norm_num)).isOpen.measurableSet,
      haxis, hinter] with x hx hr hinner
    have hb := ENNReal.ofReal_le_ofReal (scalarCylinder_energy_band_majorant hm hζ0 hζ2 hx hr hinner)
    have hIc : ENNReal.ofReal (Ec.indicator (fun _ => Cc) x) =
        Ec.indicator (fun _ => ENNReal.ofReal Cc) x := by
      by_cases h : x ∈ Ec <;> simp [h]
    have hIa : ENNReal.ofReal (Ea.indicator (fun _ => Ca) x) =
        Ea.indicator (fun _ => ENNReal.ofReal Ca) x := by
      by_cases h : x ∈ Ea <;> simp [h]
    change _ ≤ ENNReal.ofReal (Ec.indicator (fun _ => Cc) x + Ea.indicator (fun _ => Ca) x) at hb
    rw [ENNReal.ofReal_add (Set.indicator_nonneg (fun _ _ => hCc) x)
      (Set.indicator_nonneg (fun _ _ => hCa) x), hIc, hIa] at hb
    exact hb
  obtain ⟨hsc, hsa⟩ := scalarProfile_energy_scaling_bound (n := n) hm hζ0 hζ2
  have hsched : M * T ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    change (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp R) *
      ((cylinderB n)⁻¹ * Real.rpow ε (cylinderNu d ζ)) ≤ _
    simpa only [mul_assoc] using hdata.2.2.2.2
  have hconstant := scalarEnergyConstant_nonneg d hd
  have hcorevol : (volume (Ec ∩ originCube 1)).toReal ≤ (4 * ε) ^ m :=
    (scalarCoreBand_volume_bound hm hζ0 hζ2 hκ).trans
      (pow_le_pow_left₀ (by positivity) (by linarith only [hε.le]) m)
  have hannvol : (volume (Ea ∩ originCube 1)).toReal ≤ (4 * ε) ^ m :=
    scalarAnnulusBand_volume_bound hm hζ0 hζ2 hκ
  have hscale (C K a : ℝ) (hC : C = K * a * M)
      (hka : K * a * ε ^ m ≤ scalarEnergyConstant d * T) :
      C * (4 * ε) ^ m ≤ (4 : ℝ) ^ m * scalarEnergyConstant d * (1 / 2 : ℝ) ^ (n + 1) := by
    calc
      _ = (4 : ℝ) ^ m * M * (K * a * ε ^ m) := by rw [hC, mul_pow]; ring
      _ ≤ (4 : ℝ) ^ m * M * (scalarEnergyConstant d * T) :=
        mul_le_mul_of_nonneg_left hka (by positivity)
      _ = ((4 : ℝ) ^ m * scalarEnergyConstant d) * (M * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsched (mul_nonneg (by positivity) hconstant)
  have hbc := (mul_le_mul_of_nonneg_left hcorevol hCc).trans
    (hscale Cc Kc (scalarCoreValue d n ζ κ) rfl hsc)
  have hba := (mul_le_mul_of_nonneg_left hannvol hCa).trans
    (hscale Ca Ka (scalarAnnulusValue d n ζ κ) rfl hsa)
  calc
    _ ≤ ∫⁻ x in originCube 1,
        Ec.indicator (fun _ => ENNReal.ofReal Cc) x + Ea.indicator (fun _ => ENNReal.ofReal Ca) x ∂volume :=
      lintegral_mono_ae hmajor
    _ = ENNReal.ofReal (Cc * (volume (Ec ∩ originCube 1)).toReal) +
        ENNReal.ofReal (Ca * (volume (Ea ∩ originCube 1)).toReal) := by
      rw [lintegral_add_left (measurable_const.indicator hEC),
        indicator_lintegral_cube Ec hEC Cc, indicator_lintegral_cube Ea hEA Ca]
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ m * scalarEnergyConstant d * (1 / 2 : ℝ) ^ (n + 1)) +
        ENNReal.ofReal ((4 : ℝ) ^ m * scalarEnergyConstant d * (1 / 2 : ℝ) ^ (n + 1)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hbc) (ENNReal.ofReal_le_ofReal hba)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (4 : ℝ) ^ m * scalarEnergyConstant d * (1 / 2 : ℝ) ^ (n + 1))
        (by positivity)]
      congr 1
      ring

end

end CoarseDeGiorgi.SharpnessExamples
