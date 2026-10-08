import CoarseDeGiorgi.SharpnessExamples.CylinderFiniteMeans
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Finite spatial power means and positive scalar series

Minkowski's inequality is first applied to finite partial sums. Continuity of
the finite mean then passes the bound to a summable positive series.
-/

open Filter Topology
open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

/-- A finite power mean is continuous for positive exponent. -/
theorem finitePowerMean_continuous {ι : Type*} [Fintype ι] {v : ℝ} (hv : 0 < v) :
    Continuous (fun f : ι → ℝ => finitePowerMean f v) := by
  unfold finitePowerMean
  apply Continuous.rpow_const
  · apply Continuous.div_const
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).rpow_const (fun _ => Or.inr hv.le)
  · exact fun _ => Or.inr (one_div_nonneg.mpr hv.le)

/-- Minkowski for a finite sum of nonnegative spatial functions. -/
theorem finitePowerMean_finset_sum_le {ι J : Type*} [Fintype ι]
    (s : Finset J) (f : J → ι → ℝ) (hf : ∀ j i, 0 ≤ f j i)
    {v : ℝ} (hv : 1 ≤ v) :
    finitePowerMean (fun i => ∑ j ∈ s, f j i) v ≤
      ∑ j ∈ s, finitePowerMean (f j) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, finitePowerMean, Real.rpow_eq_pow, Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le hv)),
        Finset.sum_const_zero, zero_div, Real.zero_rpow (one_div_ne_zero (ne_of_gt (zero_lt_one.trans_le hv))), le_refl]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (finitePowerMean_add_le (f j) (fun i => ∑ k ∈ s, f k i) (hf j)
        (fun i => Finset.sum_nonneg (fun k _ => hf k i)) hv).trans
        (add_le_add le_rfl ih)

/-- Minkowski passes to a countable series by continuity of its finite
spatial mean, with no infinite sum taken inside a power before convergence. -/
theorem finitePowerMean_tsum_le {ι : Type*} [Fintype ι]
    (f : ℕ → ι → ℝ) (hf : ∀ j i, 0 ≤ f j i)
    (hs : ∀ i, Summable (fun j => f j i)) {v : ℝ} (hv : 1 ≤ v)
    (hm : Summable (fun j => finitePowerMean (f j) v)) :
    finitePowerMean (fun i => ∑' j, f j i) v ≤ ∑' j, finitePowerMean (f j) v := by
  have ht : Tendsto (fun N i => ∑ j ∈ Finset.range N, f j i) atTop
      (𝓝 (fun i => ∑' j, f j i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact (hs i).hasSum.tendsto_sum_nat
  have hmean := (finitePowerMean_continuous (zero_lt_one.trans_le hv)).continuousAt.tendsto.comp ht
  have hsum := hm.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto hmean hsum
    (Eventually.of_forall fun N => finitePowerMean_finset_sum_le (Finset.range N) f hf hv)

end CoarseDeGiorgi.SharpnessExamples
