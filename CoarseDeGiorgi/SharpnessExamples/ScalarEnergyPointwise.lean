module

public import CoarseDeGiorgi.SharpnessExamples.ScalarEnergyScaling

/-! # Pointwise majorants for the weighted cylinder value and gradient -/

@[expose] public section

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem scalarProfile_value_gradient_bound {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    {x : Vec d} (hx : x ∈ originCube 1)
    (hr : 0 < transverseNorm (x - cylinderCenter (cylinderB n)))
    (D : ℝ) (hD : |scalarRadialDerivative d n ζ (transverseNorm
      (x - cylinderCenter (cylinderB n)))| ≤ D) :
    scalarCylinderSubsolution n ζ x ^ 2 + vecNormSq (scalarCylinderGradient n ζ x) ≤
      (4 + 4 * (d : ℝ) * cylinderRate d n (cylinderRadialConstant d) ^ 2 + (d : ℝ) * D ^ 2) *
        (((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp (cylinderRate d n (cylinderRadialConstant d))) := by
  let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
  let R := cylinderRate d n (cylinderRadialConstant d)
  let M := ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp R
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ht : |x 0| ≤ 1 / 2 := by
    have ht := hx 0
    change -(1 / 2 : ℝ) < x 0 ∧ x 0 < 1 / 2 at ht
    exact (abs_le.mpr ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨hX, hX'⟩ := scalarAxialProfile_sq_bound (n := n) hd hζ0 hζ2 ht
  have hX'' : scalarAxialDerivative d n ζ (x 0) ^ 2 ≤ R ^ 2 * M := by
    simpa only [R, M, mul_assoc] using hX'
  have hψ := scalarRadialProfile_bounds (n := n) hd hζ0 hζ2 hr.le
  have hψ2 : scalarRadialProfile d n ζ r ^ 2 ≤ 4 := by
    nlinarith only [hψ.1, hψ.2]
  have hψ'2 : scalarRadialDerivative d n ζ r ^ 2 ≤ D ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hD 2
  have hval : scalarCylinderSubsolution n ζ x ^ 2 ≤ 4 * M := by
    change (scalarAxialProfile d n ζ (x 0) * scalarRadialProfile d n ζ r) ^ 2 ≤ _
    rw [mul_pow]
    exact (mul_le_mul hX hψ2 (sq_nonneg _) hM).trans_eq (mul_comm _ _)
  have hgrad : vecNormSq (scalarCylinderGradient n ζ x) ≤
      (d : ℝ) * (4 * R ^ 2 * M + D ^ 2 * M) := by
    apply (scalarCylinderGradient_sq_le hr).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    exact add_le_add
      ((mul_le_mul hX'' hψ2 (sq_nonneg _) (mul_nonneg (sq_nonneg R) hM)).trans_eq (by ring))
      ((mul_le_mul hX hψ'2 (sq_nonneg _) hM).trans_eq (mul_comm _ _))
  calc
    _ ≤ 4 * M + (d : ℝ) * (4 * R ^ 2 * M + D ^ 2 * M) := add_le_add hval hgrad
    _ = _ := by ring

/-- The pointwise source energy integrand on the two open bands; the
interfaces and axis are treated separately by the null-set lemmas. -/
theorem scalarCylinder_energy_band_majorant {m : ℕ} (hm : 2 ≤ m)
    {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) {x : Vec (m + 1)}
    (hx : x ∈ originCube 1)
    (hr : 0 < transverseNorm (x - cylinderCenter (cylinderB n)))
    (hinner : transverseNorm (x - cylinderCenter (cylinderB n)) ≠
      cylinderRadius (m + 1) n ζ (cylinderRadialConstant (m + 1))) :
    let d := m + 1
    let κ := cylinderRadialConstant d
    let ε := cylinderRadius d n ζ κ
    let R := cylinderRate d n κ
    let M := ((n + 1 : ℕ) : ℝ) ^ 2 * Real.exp R
    scalarSharpnessWeight ζ κ x *
        (scalarCylinderSubsolution n ζ x ^ 2 + vecNormSq (scalarCylinderGradient n ζ x)) ≤
      (scalarCoreBand n ζ κ).indicator (fun _ =>
        (4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (2 * scalarProfileXi d n ζ / ε) ^ 2) *
          scalarCoreValue d n ζ κ * M) x +
      (scalarAnnulusBand n ζ κ).indicator (fun _ =>
        (4 + 4 * (d : ℝ) * R ^ 2 + (d : ℝ) * (κ / ε) ^ 2) *
          scalarAnnulusValue d n ζ κ * M) x := by
  classical
  let d := m + 1
  let κ := cylinderRadialConstant d
  let ε := cylinderRadius d n ζ κ
  let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
  have hd : 3 ≤ d := by dsimp [d]; omega
  have hκ := cylinderRadialConstant_pos hd
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2 hκ).1
  dsimp only
  by_cases hc : r < ε
  · have hcore : x ∈ scalarCoreBand n ζ κ := hc
    have hnotann : x ∉ scalarAnnulusBand n ζ κ := fun h => (not_lt.mpr hc.le) h.1
    rw [Set.indicator_of_mem hcore, Set.indicator_of_notMem hnotann, add_zero,
      scalarSharpnessWeight_eq_core hd hζ0 hζ2 hκ hcore]
    have hb := scalarProfile_value_gradient_bound hd hζ0 hζ2 hx hr _
      (scalarRadialDerivative_core_bound hd hζ0 hζ2 hr.le hc)
    have hpos : 0 ≤ scalarCoreValue d n ζ κ := by
      unfold scalarCoreValue
      exact mul_nonneg (cylinderB_pos n).le (Real.rpow_nonneg hε.le _)
    exact (mul_le_mul_of_nonneg_left hb hpos).trans_eq (by ring)
  · by_cases ha : r < 2 * ε
    · have h1 : ε < r := lt_of_le_of_ne (le_of_not_gt hc) hinner.symm
      have hnotcore : x ∉ scalarCoreBand n ζ κ := hc
      have hann : x ∈ scalarAnnulusBand n ζ κ := ⟨h1, ha⟩
      rw [Set.indicator_of_notMem hnotcore, Set.indicator_of_mem hann, zero_add,
        scalarSharpnessWeight_eq_annulus hd hζ0 hζ2 hκ hann]
      have hb := scalarProfile_value_gradient_bound hd hζ0 hζ2 hx hr _
        (scalarRadialDerivative_annulus_bound hd hζ0 hζ2 h1 ha)
      have hpos : 0 ≤ scalarAnnulusValue d n ζ κ := by
        unfold scalarAnnulusValue
        exact mul_nonneg (inv_nonneg.mpr (cylinderB_pos n).le) (Real.rpow_nonneg hε.le _)
      exact (mul_le_mul_of_nonneg_left hb hpos).trans_eq (by ring)
    · have hnotann : x ∉ scalarAnnulusBand n ζ κ := fun h => ha h.2
      have hnotcore : x ∉ scalarCoreBand n ζ κ := hc
      rw [Set.indicator_of_notMem hnotcore, Set.indicator_of_notMem hnotann]
      have hzero := scalarRadialProfile_eq_zero hd hζ0 hζ2 (le_of_not_gt ha)
      change scalarRadialProfile (m + 1) n ζ
        (transverseNorm (x - cylinderCenter (cylinderB n))) = 0 at hzero
      rw [scalarCylinderGradient_eq_zero_outer hd hζ0 hζ2 (le_of_not_gt ha)]
      simp only [scalarCylinderSubsolution, hzero, mul_zero, zero_pow (by decide : 2 ≠ 0),
        vecNormSq, vecDot, Pi.zero_apply, Finset.sum_const_zero, add_zero, le_refl]

end

end CoarseDeGiorgi.SharpnessExamples
