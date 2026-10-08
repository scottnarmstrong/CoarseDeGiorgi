import CoarseDeGiorgi.SharpnessExamples.ScalarGradientBounds

/-! # Scalar algebra behind the summable cylinder energy bound -/

open Homogenization

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- A dimensional constant for the elementary, coordinatewise energy bound. -/
def scalarEnergyConstant (d : ℕ) : ℝ :=
  4 + 4 * (d : ℝ) * ((d : ℝ) - 1) * cylinderRadialConstant d +
    (d : ℝ) * cylinderRadialConstant d ^ 2

theorem scalarEnergyConstant_nonneg (d : ℕ) (hd : 3 ≤ d) :
    0 ≤ scalarEnergyConstant d := by
  have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hκ := cylinderRadialConstant_pos hd
  have hm : 0 ≤ (d : ℝ) - 1 := by linarith only [hdR]
  unfold scalarEnergyConstant
  positivity

private theorem radial_mass_identities {m n : ℕ} {ζ : ℝ}
    (hε : 0 < cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))) :
    let ε := cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))
    let b := cylinderB n
    let T := b⁻¹ * Real.rpow ε ((m : ℝ) - ζ)
    scalarCoreValue (m + 1) n ζ (cylinderRadialConstant (m + 1)) * ε ^ m = b ^ 2 * T ∧
    scalarAnnulusValue (m + 1) n ζ (cylinderRadialConstant (m + 1)) * ε ^ m = ε ^ 2 * T := by
  let ε := cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))
  have hb := (cylinderB_pos n).ne'
  have hcombine (u : ℝ) : Real.rpow ε u * ε ^ m = Real.rpow ε (u + (m : ℝ)) := by
    rw [← Real.rpow_natCast ε m]
    exact (Real.rpow_add hε _ _).symm
  dsimp only
  constructor
  · unfold scalarCoreValue
    change cylinderB n * Real.rpow ε (-ζ) * ε ^ m = _
    rw [mul_assoc, hcombine]
    have he : -ζ + (m : ℝ) = (m : ℝ) - ζ := by ring
    rw [he]
    field_simp
    rfl
  · unfold scalarAnnulusValue
    change (cylinderB n)⁻¹ * Real.rpow ε (2 - ζ) * ε ^ m = _
    rw [mul_assoc, hcombine]
    have hp : Real.rpow ε (2 - ζ + (m : ℝ)) = ε ^ 2 * Real.rpow ε ((m : ℝ) - ζ) := by
      calc
        _ = Real.rpow ε (2 + ((m : ℝ) - ζ)) := by congr 1; ring
        _ = Real.rpow ε 2 * Real.rpow ε ((m : ℝ) - ζ) := Real.rpow_add hε _ _
        _ = _ := by simp only [Real.rpow_eq_pow, Real.rpow_two]
    rw [hp]
    ring

/-- The core and annular mass factors, including axial and radial derivative
terms, are bounded by the same scheduled transverse power. -/
theorem scalarProfile_energy_scaling_bound {m : ℕ} (hm : 2 ≤ m) {n : ℕ} {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) :
    let d := m + 1
    let κ := cylinderRadialConstant d
    let ε := cylinderRadius d n ζ κ
    let R := cylinderRate d n κ
    let T := (cylinderB n)⁻¹ * Real.rpow ε (cylinderNu d ζ)
    (4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (2 * scalarProfileXi d n ζ / ε) ^ 2) *
        scalarCoreValue d n ζ κ * ε ^ m ≤ scalarEnergyConstant d * T ∧
    (4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (κ / ε) ^ 2) *
        scalarAnnulusValue d n ζ κ * ε ^ m ≤ scalarEnergyConstant d * T := by
  let d := m + 1
  let κ := cylinderRadialConstant d
  let ε := cylinderRadius d n ζ κ
  let b := cylinderB n
  let R := cylinderRate d n κ
  let T := b⁻¹ * Real.rpow ε (cylinderNu d ζ)
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hκ : 0 < κ := cylinderRadialConstant_pos hd
  have hdata := cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2 hκ
  have hε : 0 < ε := hdata.1
  have hb : 0 < b := cylinderB_pos n
  have hb1 : b ≤ 1 := (cylinderB_le_eighth n).trans (by norm_num)
  have hεb : ε ≤ b := by
    have hden : 1 ≤ 16 * (1 + Real.sqrt κ) := by nlinarith [Real.sqrt_nonneg κ]
    exact hdata.2.1.le.trans ((div_le_self hb.le hden))
  have hε1 : ε ≤ 1 := hεb.trans hb1
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb.le, hb1]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε.le, hε1]
  have hratio : (ε / b) ^ 2 ≤ 1 := by
    have hr : 0 ≤ ε / b := div_nonneg hε.le hb.le
    have hr1 : ε / b ≤ 1 := (div_le_one hb).2 hεb
    nlinarith only [hr, hr1]
  have hT : 0 ≤ T := mul_nonneg (inv_nonneg.mpr hb.le) (Real.rpow_nonneg hε.le _)
  have hnu : cylinderNu d ζ = (m : ℝ) - ζ := by
    dsimp [cylinderNu, d]
    push_cast
    ring
  obtain ⟨hcore, hann⟩ := radial_mass_identities (m := m) (n := n) (ζ := ζ) hε
  change scalarCoreValue d n ζ κ * ε ^ m = b ^ 2 * (b⁻¹ * Real.rpow ε ((m : ℝ) - ζ)) at hcore
  change scalarAnnulusValue d n ζ κ * ε ^ m = ε ^ 2 * (b⁻¹ * Real.rpow ε ((m : ℝ) - ζ)) at hann
  rw [← hnu] at hcore hann
  change scalarCoreValue d n ζ κ * ε ^ m = b ^ 2 * T at hcore
  change scalarAnnulusValue d n ζ κ * ε ^ m = ε ^ 2 * T at hann
  have hR : R ^ 2 = (m : ℝ) * κ / b ^ 2 := by
    dsimp [R, cylinderRate]
    rw [div_pow, Real.sq_sqrt (by
      have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      dsimp [d]
      push_cast
      nlinarith only [hmR, hκ.le])]
    congr 1
    dsimp [d]
    push_cast
    ring
  have hξ : 2 * scalarProfileXi d n ζ / ε = κ * ε / b ^ 2 := by
    dsimp [scalarProfileXi]
    change 2 * (κ / 2 * (ε / b) ^ 2) / ε = _
    field_simp [hb.ne', hε.ne']
  have hC0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hmc : 0 ≤ (m : ℝ) * κ := mul_nonneg (Nat.cast_nonneg _) hκ.le
  have hCr : 0 ≤ (d : ℝ) * κ ^ 2 := mul_nonneg hC0 (sq_nonneg κ)
  dsimp only
  change _ ≤ scalarEnergyConstant d * T ∧ _ ≤ scalarEnergyConstant d * T
  constructor
  · have heq : (4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (2 * scalarProfileXi d n ζ / ε) ^ 2) *
        scalarCoreValue d n ζ κ * ε ^ m =
        (4 * b ^ 2 + 4 * (d : ℝ) * (m : ℝ) * κ + (d : ℝ) * κ ^ 2 * (ε / b) ^ 2) * T := by
      rw [mul_assoc, hcore, hR, hξ]
      field_simp [hb.ne']
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ hT
    unfold scalarEnergyConstant
    have hdR : (d : ℝ) - 1 = (m : ℝ) := by dsimp [d]; push_cast; ring
    rw [hdR]
    change _ ≤ 4 + 4 * (d : ℝ) * (m : ℝ) * κ + (d : ℝ) * κ ^ 2
    exact add_le_add (add_le_add (by linarith only [hb2]) le_rfl)
      (mul_le_of_le_one_right hCr hratio)
  · have heq : (4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (κ / ε) ^ 2) *
        scalarAnnulusValue d n ζ κ * ε ^ m =
        (4 * ε ^ 2 + 4 * (d : ℝ) * (m : ℝ) * κ * (ε / b) ^ 2 + (d : ℝ) * κ ^ 2) * T := by
      rw [mul_assoc, hann, hR]
      field_simp [hb.ne', hε.ne']
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ hT
    unfold scalarEnergyConstant
    have hdR : (d : ℝ) - 1 = (m : ℝ) := by dsimp [d]; push_cast; ring
    rw [hdR]
    change _ ≤ 4 + 4 * (d : ℝ) * (m : ℝ) * κ + (d : ℝ) * κ ^ 2
    exact add_le_add (add_le_add (by linarith only [hε2])
      (mul_le_of_le_one_right (by positivity) hratio)) le_rfl

end

end CoarseDeGiorgi.SharpnessExamples
