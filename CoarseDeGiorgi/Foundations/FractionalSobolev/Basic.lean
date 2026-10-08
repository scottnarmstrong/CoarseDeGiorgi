import CoarseDeGiorgi.Statements.FracKernel
import CoarseDeGiorgi.Statements.DnpvCriticalExponent
import Homogenization.Multiscale.CubeAverage
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace CoarseDeGiorgi.Foundations.FractionalSobolev

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

theorem euclidDist_nonneg {n : ℕ} (x y : Vec n) : 0 ≤ euclidDist x y :=
  Real.sqrt_nonneg _

theorem euclidDist_pos {n : ℕ} {x y : Vec n} (h : x ≠ y) : 0 < euclidDist x y := by
  have hex : ∃ i, x i ≠ y i := by
    by_contra hn
    push Not at hn
    exact h (funext hn)
  obtain ⟨i, hi⟩ := hex
  apply Real.sqrt_pos.mpr
  have hb := sq_apply_le_vecNormSq (x - y) i
  have hs : 0 < (x i - y i) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hi)
  exact hs.trans_le hb

theorem euclidDist_le_of_mem_ball {n : ℕ} {x y : Vec n} {r : ℝ}
    (hr : 0 < r) (hy : y ∈ Metric.ball x r) :
    euclidDist x y ≤ Real.sqrt (n : ℝ) * r := by
  have hcoord : ∀ i, |x i - y i| ≤ r := by
    intro i
    have h := dist_le_pi_dist x y i
    rw [Real.dist_eq] at h
    exact h.trans (by simpa only [dist_comm] using (Metric.mem_ball.mp hy).le)
  have hsq : vecNormSq (x - y) ≤ (n : ℝ) * r ^ 2 := by
    unfold vecNormSq vecDot
    calc
      (∑ i : Fin n, (x - y) i * (x - y) i) ≤ ∑ _i : Fin n, r ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := abs_le.mp (hcoord i)
        change (x i - y i) * (x i - y i) ≤ r ^ 2
        nlinarith only [hi.1, hi.2, hr]
      _ = (n : ℝ) * r ^ 2 := by simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
  unfold euclidDist
  calc
    Real.sqrt (vecNormSq (x - y)) ≤ Real.sqrt ((n : ℝ) * r ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (n : ℝ) * r := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq_eq_abs, abs_of_pos hr]

end

end CoarseDeGiorgi.Foundations.FractionalSobolev
