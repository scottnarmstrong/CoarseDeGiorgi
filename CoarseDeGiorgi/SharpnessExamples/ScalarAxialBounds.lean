import CoarseDeGiorgi.SharpnessExamples.ScalarProfileCalculus

/-! # Quantitative axial bounds for the source's hyperbolic cosine profiles -/

open Homogenization

namespace CoarseDeGiorgi.SharpnessExamples

theorem cylinderRate_nonneg (d n : ℕ) (κ : ℝ) : 0 ≤ cylinderRate d n κ := by
  unfold cylinderRate
  exact div_nonneg (Real.sqrt_nonneg _) (cylinderB_pos n).le

private theorem cosh_sinh_exp_bound {R t : ℝ} (hR : 0 ≤ R) (ht : |t| ≤ 1 / 2) :
    Real.cosh (R * t) ≤ Real.exp (R / 2) ∧ |Real.sinh (R * t)| ≤ Real.exp (R / 2) := by
  have h1 : R * t ≤ R / 2 := by
    have h := mul_le_mul_of_nonneg_left (le_abs_self t |>.trans ht) hR
    linarith only [h]
  have h2 : -(R * t) ≤ R / 2 := by
    have h := mul_le_mul_of_nonneg_left (neg_le_abs t |>.trans ht) hR
    linarith only [h]
  have he1 := Real.exp_le_exp.mpr h1
  have he2 := Real.exp_le_exp.mpr h2
  constructor
  · rw [Real.cosh_eq]
    linarith only [he1, he2]
  · rw [Real.sinh_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hb : |Real.exp (R * t) - Real.exp (-(R * t))| ≤
        Real.exp (R * t) + Real.exp (-(R * t)) := by
      exact (abs_sub _ _).trans (by rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)])
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith only [hb, he1, he2])

/-- Uniform value and derivative bounds on the axial interval of the unit
cube, with the exact source rate. -/
theorem scalarAxialProfile_exp_bounds {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ t : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (ht : |t| ≤ 1 / 2) :
    |scalarAxialProfile d n ζ t| ≤ ((n + 1 : ℕ) : ℝ) *
      Real.exp (cylinderRate d n (cylinderRadialConstant d) / 2) ∧
    |scalarAxialDerivative d n ζ t| ≤
      cylinderRate d n (cylinderRadialConstant d) * ((n + 1 : ℕ) : ℝ) *
        Real.exp (cylinderRate d n (cylinderRadialConstant d) / 2) := by
  let R := cylinderRate d n (cylinderRadialConstant d)
  let j : ℝ := ((n + 1 : ℕ) : ℝ)
  let A := j / (1 + scalarProfileXi d n ζ)
  have hξ := (scalarProfileXi_bounds (n := n) hd hζ0 hζ2).1
  have hj : 0 ≤ j := Nat.cast_nonneg _
  have hA0 : 0 ≤ A := div_nonneg hj (by linarith only [hξ])
  have hAj : A ≤ j := by
    apply div_le_self hj
    linarith only [hξ]
  have hR := cylinderRate_nonneg d n (cylinderRadialConstant d)
  obtain ⟨hcosh, hsinh⟩ := cosh_sinh_exp_bound hR ht
  constructor
  · change |A * Real.cosh (R * t)| ≤ _
    rw [abs_mul, abs_of_nonneg hA0, abs_of_pos (Real.cosh_pos _)]
    exact mul_le_mul hAj hcosh (Real.cosh_pos _).le hj
  · change |A * R * Real.sinh (R * t)| ≤ _
    rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg hR]
    calc
      _ ≤ (j * R) * Real.exp (R / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hAj hR) hsinh (abs_nonneg _) (mul_nonneg hj hR)
      _ = _ := by ring

/-- The squared axial amplitude has precisely the `j² exp(rate)` upper bound
used in the radius schedule. -/
theorem scalarAxialProfile_sq_bound {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ t : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (ht : |t| ≤ 1 / 2) :
    scalarAxialProfile d n ζ t ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (cylinderRate d n (cylinderRadialConstant d)) ∧
    scalarAxialDerivative d n ζ t ^ 2 ≤
      cylinderRate d n (cylinderRadialConstant d) ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (cylinderRate d n (cylinderRadialConstant d)) := by
  obtain ⟨hX, hD⟩ := scalarAxialProfile_exp_bounds hd hζ0 hζ2 ht
  have hexp (R : ℝ) : Real.exp (R / 2) ^ 2 = Real.exp R := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  constructor
  · have h := pow_le_pow_left₀ (abs_nonneg _) hX 2
    simpa only [sq_abs, mul_pow, hexp] using h
  · have h := pow_le_pow_left₀ (abs_nonneg _) hD 2
    simpa only [sq_abs, mul_pow, hexp, mul_assoc] using h

end CoarseDeGiorgi.SharpnessExamples
