import CoarseDeGiorgi.SharpnessExamples.ScalarGradient
import CoarseDeGiorgi.SharpnessExamples.ScalarAxialBounds

/-! # Quantitative radial and gradient bounds in each cylinder region -/

open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Sharpness
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

theorem scalarRadialDerivative_core_bound {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (hr0 : 0 ≤ r)
    (hr : r < cylinderRadius d n ζ (cylinderRadialConstant d)) :
    |scalarRadialDerivative d n ζ r| ≤
      2 * scalarProfileXi d n ζ / cylinderRadius d n ζ (cylinderRadialConstant d) := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have hξ := (scalarProfileXi_bounds (n := n) hd hζ0 hζ2).1
  unfold scalarRadialDerivative
  rw [ite_eq_left hr, abs_div, abs_mul, abs_mul]
  rw [abs_of_nonneg hr0, abs_of_nonneg (sq_nonneg (cylinderRadius d n ζ (cylinderRadialConstant d))), abs_of_pos hξ]
  norm_num
  apply (div_le_iff₀ (sq_pos_of_pos hε)).2
  calc
    2 * scalarProfileXi d n ζ * r ≤ 2 * scalarProfileXi d n ζ * ε :=
      mul_le_mul_of_nonneg_left hr.le (by positivity)
    _ = (2 * scalarProfileXi d n ζ / ε) * ε ^ 2 := by field_simp

theorem scalarRadialDerivative_annulus_bound {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hr1 : cylinderRadius d n ζ (cylinderRadialConstant d) < r)
    (hr2 : r < 2 * cylinderRadius d n ζ (cylinderRadialConstant d)) :
    |scalarRadialDerivative d n ζ r| ≤
      cylinderRadialConstant d / cylinderRadius d n ζ (cylinderRadialConstant d) := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have hκ := cylinderRadialConstant_pos hd
  have hratio : 1 ≤ r / ε := (le_div_iff₀ hε).2 (by simpa only [one_mul] using hr1.le)
  have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hp : Real.rpow (r / ε) (2 - (d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hratio (by linarith only [hdR])
  have hp0 : 0 ≤ Real.rpow (r / ε) (2 - (d : ℝ)) :=
    Real.rpow_nonneg (zero_le_one.trans hratio) _
  unfold scalarRadialDerivative
  rw [ite_eq_right (not_lt.mpr hr1.le), ite_eq_left hr2, abs_mul, abs_div,
    abs_neg, abs_of_pos hκ, abs_of_pos hε, abs_of_nonneg hp0]
  exact mul_le_of_le_one_right (div_nonneg hκ.le hε.le) hp

/-- A dimensional bound for the squared gradient follows coordinatewise;
the proof does not need a polar integration formula. -/
theorem scalarCylinderGradient_sq_le {d : ℕ} [NeZero d] {n : ℕ} {ζ : ℝ} {x : Vec d}
    (hr : 0 < transverseNorm (x - cylinderCenter (cylinderB n))) :
    vecNormSq (scalarCylinderGradient n ζ x) ≤ (d : ℝ) *
      (scalarAxialDerivative d n ζ (x 0) ^ 2 *
        scalarRadialProfile d n ζ (transverseNorm (x - cylinderCenter (cylinderB n))) ^ 2 +
       scalarAxialProfile d n ζ (x 0) ^ 2 *
        scalarRadialDerivative d n ζ (transverseNorm (x - cylinderCenter (cylinderB n))) ^ 2) := by
  let r := transverseNorm (x - cylinderCenter (d := d) (cylinderB n))
  let A := scalarAxialDerivative d n ζ (x 0) ^ 2 * scalarRadialProfile d n ζ r ^ 2
  let B := scalarAxialProfile d n ζ (x 0) ^ 2 * scalarRadialDerivative d n ζ r ^ 2
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hcoord (i : Fin d) : scalarCylinderGradient n ζ x i ^ 2 ≤ A + B := by
    by_cases hi : i = 0
    · simpa only [scalarCylinderGradient, ite_eq_left hi, mul_pow, A, r] using le_add_of_nonneg_right hB
    · have hiV : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have hbound := abs_transverse_coordinate_le (x - cylinderCenter (cylinderB n)) i hiV
      have hratio : |(x - cylinderCenter (d := d) (cylinderB n)) i / r| ≤ 1 := by
        rw [abs_div, abs_of_pos hr]
        exact (div_le_one hr).2 hbound
      have hsquare : ((x - cylinderCenter (d := d) (cylinderB n)) i / r) ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hratio 2
      calc
        _ = B * ((x - cylinderCenter (d := d) (cylinderB n)) i / r) ^ 2 := by
          simp only [scalarCylinderGradient, ite_eq_right hi, mul_pow, B, r]
        _ ≤ B := mul_le_of_le_one_right hB hsquare
        _ ≤ A + B := le_add_of_nonneg_left hA
  calc
    _ = ∑ i : Fin d, scalarCylinderGradient n ζ x i ^ 2 := by
      simp only [vecNormSq, vecDot, pow_two]
    _ ≤ ∑ _i : Fin d, (A + B) := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (d : ℝ) * (A + B) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem scalarCylinderGradient_eq_zero_outer {d : ℕ} [NeZero d] (hd : 3 ≤ d)
    {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) {x : Vec d}
    (hr : 2 * cylinderRadius d n ζ (cylinderRadialConstant d) ≤
      transverseNorm (x - cylinderCenter (cylinderB n))) :
    scalarCylinderGradient n ζ x = 0 := by
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have h1 : ¬ transverseNorm (x - cylinderCenter (cylinderB n)) <
      cylinderRadius d n ζ (cylinderRadialConstant d) := by linarith
  ext i
  simp only [scalarCylinderGradient, scalarRadialDerivative, ite_eq_right h1,
    ite_eq_right (not_lt.mpr hr), scalarRadialProfile_eq_zero hd hζ0 hζ2 hr,
    mul_zero, zero_mul, ite_self, Pi.zero_apply]

end CoarseDeGiorgi.SharpnessExamples
