module

public import CoarseDeGiorgi.Harnack.Iterations.RadiusSums
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- The finite product of exponential step costs is the exponential of the
geometrically weighted sum, divided by the initial exponent.
-/
theorem geometric_exponential_cost_product {χ b : ℝ}
    (hχ : 0 < χ) (hb : 0 < b) (L : ℕ → ℝ) (N : ℕ) :
    (∏ j ∈ Finset.range N,
      (ENNReal.ofReal (Real.exp (L j))) ^ (1 / (b * χ ^ j))) =
      ENNReal.ofReal (Real.exp
        ((∑ j ∈ Finset.range N, (χ⁻¹) ^ j * L j) / b)) := by
  have hterm (j : ℕ) :
      (ENNReal.ofReal (Real.exp (L j))) ^ (1 / (b * χ ^ j)) =
        ENNReal.ofReal (Real.exp (((χ⁻¹) ^ j * L j) / b)) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    rw [inv_pow]
    field_simp
  simp_rw [hterm]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, ← Finset.sum_div]

/-- Any powered chain whose costs are bounded by a prescribed logarithmic
sequence inherits its finite logarithmic envelope.
-/
theorem geometric_cost_product_le {χ b B : ℝ}
    (hχ : 0 < χ) (hb : 0 < b) (L : ℕ → ℝ) (K : ℕ → ℝ≥0∞)
    (N : ℕ) (hK : ∀ j < N, K j ≤ ENNReal.ofReal (Real.exp (L j)))
    (hL : (∑ j ∈ Finset.range N, (χ⁻¹) ^ j * L j) ≤ B) :
    (∏ j ∈ Finset.range N, K j ^ (1 / (b * χ ^ j))) ≤
      ENNReal.ofReal (Real.exp (B / b)) := by
  calc
    _ ≤ ∏ j ∈ Finset.range N,
        (ENNReal.ofReal (Real.exp (L j))) ^ (1 / (b * χ ^ j)) := by
      apply Finset.prod_le_prod
      intro j hj
      exact ENNReal.rpow_le_rpow (hK j (Finset.mem_range.mp hj)) (by positivity)
    _ = _ := geometric_exponential_cost_product hχ hb L N
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hL hb.le))

/-- Convert the logarithmic envelope into the literal source gap power.
-/
theorem exponential_gap_factor_identity {C g δ b D : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (_hD : 0 < D) :
    ENNReal.ofReal (Real.exp ((C + g * Real.log (1 / δ)) / b)) *
        (ENNReal.ofReal D) ^ (1 / b) =
      (ENNReal.ofReal ((D * Real.exp C) * δ ^ (-g))) ^ (1 / b) := by
  have heq : Real.exp (C + g * Real.log (1 / δ)) = Real.exp C * δ ^ (-g) := by
    rw [Real.exp_add, Real.rpow_def_of_pos hδ, one_div, Real.log_inv]
    congr 2
    ring
  have hroot : ENNReal.ofReal (Real.exp ((C + g * Real.log (1 / δ)) / b)) =
      (ENNReal.ofReal (Real.exp (C + g * Real.log (1 / δ)))) ^ (1 / b) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    ring
  rw [hroot, ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / b), heq,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp C * δ ^ (-g))]
  congr 2
  ring

end CoarseDeGiorgi.Harnack.Iterations
