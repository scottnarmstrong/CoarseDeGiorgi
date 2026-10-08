module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Minkowski over a series and Hölder over a finite index set

Pure inequalities in `ℝ≥0∞` used when the local bounds are summed over a cover. -/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open scoped BigOperators ENNReal
open Filter Topology
noncomputable section

variable {ι : Type*}

/-- Minkowski's inequality for finite partial sums over `k`. -/
theorem minkowski_range (Z : Finset ι) (a : ℕ → ι → ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) (N : ℕ) :
    (∑ z ∈ Z, (∑ k ∈ Finset.range N, a k z) ^ r) ^ (1 / r) ≤
      ∑ k ∈ Finset.range N, (∑ z ∈ Z, a k z ^ r) ^ (1 / r) := by
  induction N with
  | zero =>
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    simp [ENNReal.zero_rpow_of_pos hr0, hr0]
  | succ N ih =>
    rw [Finset.sum_range_succ (fun k => (∑ z ∈ Z, a k z ^ r) ^ (1 / r))]
    refine le_trans ?_ (add_le_add_left ih _)
    simp only [Finset.sum_range_succ]
    exact ENNReal.Lp_add_le Z (fun z => ∑ k ∈ Finset.range N, a k z) (fun z => a N z) hr

/-- Minkowski's inequality for a series in `k`, with `ℓʳ` norm over a finite index set. -/
theorem minkowski_tsum (Z : Finset ι) (a : ℕ → ι → ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    (∑ z ∈ Z, (∑' k, a k z) ^ r) ^ (1 / r) ≤
      ∑' k, (∑ z ∈ Z, a k z ^ r) ^ (1 / r) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hlim : Tendsto (fun N => ∑ z ∈ Z, (∑ k ∈ Finset.range N, a k z) ^ r) atTop
      (𝓝 (∑ z ∈ Z, (∑' k, a k z) ^ r)) := by
    refine tendsto_finsetSum _ fun z _ => ?_
    exact ((ENNReal.continuous_rpow_const (y := r)).tendsto _).comp (ENNReal.tendsto_nat_tsum _)
  have hbound : ∀ N, ∑ z ∈ Z, (∑ k ∈ Finset.range N, a k z) ^ r ≤
      (∑' k, (∑ z ∈ Z, a k z ^ r) ^ (1 / r)) ^ r := by
    intro N
    have h1 := minkowski_range Z a hr N
    have h2 : ∑ k ∈ Finset.range N, (∑ z ∈ Z, a k z ^ r) ^ (1 / r) ≤
        ∑' k, (∑ z ∈ Z, a k z ^ r) ^ (1 / r) := ENNReal.sum_le_tsum _
    have h3 := ENNReal.rpow_le_rpow (h1.trans h2) hr0.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one] at h3
    exact h3
  have hle := le_of_tendsto' hlim hbound
  have h4 := ENNReal.rpow_le_rpow hle (one_div_nonneg.mpr hr0.le)
  rwa [← ENNReal.rpow_mul, mul_one_div, div_self hr0.ne', ENNReal.rpow_one] at h4

/-- Hölder over the finite index set, with `1/r = 1/(2q) + 1/2`. -/
theorem holder_pair (Z : Finset ι) (T E : ι → ℝ≥0∞) {q r : ℝ} (hq : 1 < q)
    (hr : r = 2 * q / (q + 1)) :
    (∑ z ∈ Z, (T z ^ (1 / (2 * q)) * E z ^ (1 / 2 : ℝ)) ^ r) ^ (1 / r) ≤
      (∑ z ∈ Z, T z) ^ (1 / (2 * q)) * (∑ z ∈ Z, E z) ^ (1 / 2 : ℝ) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr0 : 0 < r := by rw [hr]; positivity
  have hconj : (q + 1).HolderConjugate ((q + 1) / q) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    field_simp
    ring
  have hh := ENNReal.inner_le_Lp_mul_Lq Z (fun z => T z ^ (r / (2 * q))) (fun z => E z ^ (r / 2)) hconj
  have e1 : ∀ z, (T z ^ (1 / (2 * q)) * E z ^ (1 / 2 : ℝ)) ^ r =
      T z ^ (r / (2 * q)) * E z ^ (r / 2) := by
    intro z
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    congr 2 <;> ring
  have e2 : ∀ z, (T z ^ (r / (2 * q))) ^ (q + 1) = T z := by
    intro z
    rw [← ENNReal.rpow_mul]
    have : r / (2 * q) * (q + 1) = 1 := by rw [hr]; field_simp
    rw [this, ENNReal.rpow_one]
  have e3 : ∀ z, (E z ^ (r / 2)) ^ ((q + 1) / q) = E z := by
    intro z
    rw [← ENNReal.rpow_mul]
    have : r / 2 * ((q + 1) / q) = 1 := by rw [hr]; field_simp
    rw [this, ENNReal.rpow_one]
  simp only [e1, e2, e3] at hh ⊢
  have h4 := ENNReal.rpow_le_rpow hh (one_div_nonneg.mpr hr0.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr0.le), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at h4
  have c1 : 1 / (q + 1) * (1 / r) = 1 / (2 * q) := by rw [hr]; field_simp
  have c2 : 1 / ((q + 1) / q) * (1 / r) = 1 / 2 := by rw [hr]; field_simp
  rw [c1, c2] at h4
  exact h4

end
end CoarseDeGiorgi.Localization
