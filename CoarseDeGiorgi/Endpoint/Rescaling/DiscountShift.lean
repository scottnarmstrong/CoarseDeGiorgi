module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Shifted nonnegative series bounds, including the exceptional scale-zero term. -/

@[expose] public section

open scoped ENNReal

namespace CoarseDeGiorgi.Endpoint.Rescaling

theorem discounted_shift_bound (f g : ℕ → ℝ≥0∞) (A B w : ℝ≥0∞)
    (hw0 : w ≠ 0) (hwtop : w ≠ ⊤)
    (hzero : f 0 ≤ B * f 1) (hshift : ∀ k, f (k + 1) ≤ A * g (k + 4)) :
    (∑' k, w ^ k * f k) ≤
      (B * A * (w ^ 4)⁻¹ + A * (w ^ 3)⁻¹) * ∑' k, w ^ k * g k := by
  have hc4 : (w ^ 4)⁻¹ * w ^ 4 = 1 :=
    ENNReal.inv_mul_cancel (pow_ne_zero _ hw0) (ENNReal.pow_ne_top hwtop)
  have hc3 : (w ^ 3)⁻¹ * w ^ 3 = 1 :=
    ENNReal.inv_mul_cancel (pow_ne_zero _ hw0) (ENNReal.pow_ne_top hwtop)
  have htail : (∑' k, w ^ (k + 1) * f (k + 1)) ≤
      A * (w ^ 3)⁻¹ * ∑' k, w ^ k * g k := by
    calc
      _ ≤ ∑' k, w ^ (k + 1) * (A * g (k + 4)) :=
        ENNReal.tsum_le_tsum (fun k => mul_le_mul_right (hshift k) _)
      _ = A * (w ^ 3)⁻¹ * ∑' k, w ^ (k + 4) * g (k + 4) := by
        rw [← ENNReal.tsum_mul_left]
        congr 1
        funext k
        have hp : w ^ (k + 4) = w ^ (k + 1) * w ^ 3 := by
          rw [show k + 4 = (k + 1) + 3 by omega, pow_add]
        rw [hp]
        calc
          _ = A * w ^ (k + 1) * g (k + 4) := by ac_rfl
          _ = (A * w ^ (k + 1) * g (k + 4)) * ((w ^ 3)⁻¹ * w ^ 3) := by rw [hc3, mul_one]
          _ = _ := by ac_rfl
      _ ≤ _ := mul_le_mul_right
        (ENNReal.summable.tsum_le_tsum_of_inj (g := fun k => w ^ k * g k) (fun k => k + 4) (fun _ _ h => Nat.add_right_cancel h)
          (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable) _
  have hz : f 0 ≤ B * A * (w ^ 4)⁻¹ * ∑' k, w ^ k * g k := by
    calc
      _ ≤ B * (A * g 4) := hzero.trans (mul_le_mul_right (hshift 0) B)
      _ = B * A * (w ^ 4)⁻¹ * (w ^ 4 * g 4) := by
        calc
          _ = B * A * g 4 := by ac_rfl
          _ = (B * A * g 4) * ((w ^ 4)⁻¹ * w ^ 4) := by rw [hc4, mul_one]
          _ = _ := by ac_rfl
      _ ≤ _ := mul_le_mul_right (ENNReal.le_tsum (f := fun k => w ^ k * g k) 4) _
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [pow_zero, one_mul]
  exact (add_le_add hz htail).trans_eq (add_mul _ _ _).symm

end CoarseDeGiorgi.Endpoint.Rescaling
