import CoarseDeGiorgi.Moments.Cells
import CoarseDeGiorgi.Foundations.Simplex.Partition

/-! # A sup-norm ball inside every Kuhn simplex -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory

variable {d : ℕ}

theorem kuhn_ball (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) :
    ∃ c₀ : Vec d, ∀ y : Vec d, (∀ i, |y i - c₀ i| < (3 : ℝ) ^ n / (2 * (d + 1))) →
      y ∈ Foundations.Simplex.kuhnSimplex n π z := by
  set s : ℝ := (3 : ℝ) ^ n with hs
  have hs0 : 0 < s := zpow_pos (by norm_num) n
  have hd0 : (0 : ℝ) < d + 1 := by positivity
  refine ⟨fun i => z i + s * (-1 / 2 + (((π.symm i : ℕ) : ℝ) + 1) / (d + 1)), ?_⟩
  intro y hy
  have hdelta : ∀ i, |y i - (z i + s * (-1 / 2 + (((π.symm i : ℕ) : ℝ) + 1) / (d + 1)))| <
      s / (2 * (d + 1)) := hy
  refine ⟨fun i => ?_, ?_⟩
  · have h := abs_lt.mp (hdelta i)
    have hm : ((π.symm i : ℕ) : ℝ) + 1 ≤ d := by
      have := (π.symm i).isLt
      exact_mod_cast this
    have hm0 : (0 : ℝ) ≤ ((π.symm i : ℕ) : ℝ) := Nat.cast_nonneg _
    have e1 : (1 : ℝ) / (d + 1) ≤ (((π.symm i : ℕ) : ℝ) + 1) / (d + 1) := by
      apply div_le_div_of_nonneg_right _ hd0.le; linarith
    have e2 : (((π.symm i : ℕ) : ℝ) + 1) / (d + 1) ≤ (d : ℝ) / (d + 1) :=
      div_le_div_of_nonneg_right hm hd0.le
    have e3 : (d : ℝ) / (d + 1) = 1 - 1 / (d + 1) := by field_simp; ring
    have e4 : s / (2 * (d + 1)) = s * (1 / (d + 1)) / 2 := by field_simp
    have hpos : 0 < 1 / ((d : ℝ) + 1) := by positivity
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left e1 hs0.le, mul_pos hs0 hpos]
    · nlinarith [mul_le_mul_of_nonneg_left e2 hs0.le, mul_pos hs0 hpos]
  · intro i j hij
    have hi := abs_lt.mp (hdelta (π i))
    have hj := abs_lt.mp (hdelta (π j))
    simp only [Equiv.symm_apply_apply] at hi hj
    have hij' : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast hij
    have e1 : s * ((((i : ℕ) : ℝ) + 1) / (d + 1)) + s / (d + 1) ≤ s * ((((j : ℕ) : ℝ) + 1) / (d + 1)) := by
      have : (((i : ℕ) : ℝ) + 1) / (d + 1) + 1 / (d + 1) ≤ (((j : ℕ) : ℝ) + 1) / (d + 1) := by
        rw [← add_div]; apply div_le_div_of_nonneg_right _ hd0.le; linarith
      have := mul_le_mul_of_nonneg_left this hs0.le
      rw [mul_add] at this
      calc _ = s * ((((i : ℕ) : ℝ) + 1) / (d + 1)) + s * (1 / (d + 1)) := by ring
        _ ≤ _ := this
    have e4 : s / (2 * (d + 1)) * 2 = s / (d + 1) := by field_simp
    show (fun i => y (π i) - z (π i)) i < (fun i => y (π i) - z (π i)) j
    simp only
    nlinarith [hi.1, hi.2, hj.1, hj.2]

end CoarseDeGiorgi.Cubical
