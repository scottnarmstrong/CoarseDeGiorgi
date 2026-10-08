module

public import Mathlib.Analysis.MeanInequalities

/-! Finite Hölder arithmetic for `e.lower.spatial.holder`.
The weights are abstract: no response matrix is selected here. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open scoped BigOperators

/-- The two powers in the spatial Hölder argument add to one. -/
theorem spatial_holder_exponents {q : ℝ} (hq : 1 < q) :
    let r := 2 * q / (q + 1)
    0 < r / (2 * q) ∧ 0 < r / 2 ∧ r / (2 * q) + r / 2 = 1 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hden : q + 1 ≠ 0 := ne_of_gt (by linarith only [hq0])
  dsimp only
  constructor
  · positivity
  constructor
  · positivity
  · field_simp
    ring

/-- Hölder in the exact powers r/(2q), r/2, before inserting cell volumes. -/
theorem spatial_holder {ι : Type*} (s : Finset ι) (A E : ι → ℝ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hE : ∀ i ∈ s, 0 ≤ E i)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hbalance : r / (2 * q) + r / 2 = 1) :
    (∑ i ∈ s, (A i) ^ (r / (2 * q)) * (E i) ^ (r / 2)) ≤
      (∑ i ∈ s, A i) ^ (r / (2 * q)) * (∑ i ∈ s, E i) ^ (r / 2) := by
  have ht : 0 < r / (2 * q) := div_pos hr (mul_pos (by norm_num) hq)
  have hu : 0 < r / 2 := div_pos hr (by norm_num)
  have ht1 : r / (2 * q) < 1 := by linarith only [hu, hbalance]
  have hc : Real.HolderConjugate (r / (2 * q))⁻¹ (r / 2)⁻¹ := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_inv₀ ht).mpr ht1
    · simpa only [one_div, inv_inv] using hbalance
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hc
    (f := fun i => (A i) ^ (r / (2 * q)))
    (g := fun i => (E i) ^ (r / 2))
    (fun i hi => Real.rpow_nonneg (hA i hi) _)
    (fun i hi => Real.rpow_nonneg (hE i hi) _)
  have heA : (∑ i ∈ s, ((A i) ^ (r / (2 * q))) ^ (r / (2 * q))⁻¹) =
      ∑ i ∈ s, A i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.rpow_rpow_inv (hA i hi) ht.ne'
  have heE : (∑ i ∈ s, ((E i) ^ (r / 2)) ^ (r / 2)⁻¹) = ∑ i ∈ s, E i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Real.rpow_rpow_inv (hE i hi) hu.ne'
  rw [heA, heE] at h
  simp only [one_div, inv_inv] at h
  exact h

/-- Inserting the cell volume in the mean-gradient estimate gives the source
summand `(v B^q)^(r/(2q)) E^(r/2)`. -/
theorem spatial_holder_summand {v B E M r q : ℝ}
    (hv : 0 < v) (hB : 0 ≤ B) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hr : 0 < r) (hq : 0 < q)
    (hbalance : r / (2 * q) + r / 2 = 1)
    (hmean : v * M ^ 2 ≤ B * E) :
    v * M ^ r ≤ (v * B ^ q) ^ (r / (2 * q)) * E ^ (r / 2) := by
  have hqθ : q * (r / (2 * q)) = r / 2 := by
    field_simp
  have htwo : (2 : ℝ) * (r / 2) = r := by ring
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (mul_nonneg hv.le (sq_nonneg M)) hmean
      (div_nonneg hr.le (by norm_num : (0 : ℝ) ≤ 2)))
    (Real.rpow_nonneg hv.le (r / (2 * q)))
  have hleft : v ^ (r / (2 * q)) * (v * M ^ 2) ^ (r / 2) = v * M ^ r := by
    rw [Real.mul_rpow hv.le (sq_nonneg M), ← mul_assoc,
      ← Real.rpow_add hv, hbalance, Real.rpow_one,
      ← Real.rpow_natCast M 2, ← Real.rpow_mul hM]
    norm_num only [Nat.cast_ofNat]
    rw [htwo]
  have hright : v ^ (r / (2 * q)) * (B * E) ^ (r / 2) =
      (v * B ^ q) ^ (r / (2 * q)) * E ^ (r / 2) := by
    rw [Real.mul_rpow hB hE, Real.mul_rpow hv.le (Real.rpow_nonneg hB q),
      ← Real.rpow_mul hB, hqθ, mul_assoc]
  rw [hleft, hright] at h
  exact h

/-- The r-th power of the spatial estimate, for abstract nonnegative per-cell
response weights B and per-cell energies E. -/
theorem lower_spatial_holder {ι : Type*} (s : Finset ι) (v B E M : ι → ℝ)
    (hv : ∀ i ∈ s, 0 < v i) (hB : ∀ i ∈ s, 0 ≤ B i)
    (hE : ∀ i ∈ s, 0 ≤ E i) (hM : ∀ i ∈ s, 0 ≤ M i)
    {r q : ℝ} (hr : 0 < r) (hq : 0 < q)
    (hbalance : r / (2 * q) + r / 2 = 1)
    (hmean : ∀ i ∈ s, v i * M i ^ 2 ≤ B i * E i) :
    (∑ i ∈ s, v i * M i ^ r) ≤
      (∑ i ∈ s, v i * B i ^ q) ^ (r / (2 * q)) *
        (∑ i ∈ s, E i) ^ (r / 2) := by
  refine (Finset.sum_le_sum fun i hi => spatial_holder_summand
    (hv i hi) (hB i hi) (hE i hi) (hM i hi) hr hq hbalance (hmean i hi)).trans ?_
  exact spatial_holder s (fun i => v i * B i ^ q) E
    (fun i hi => mul_nonneg (hv i hi).le (Real.rpow_nonneg (hB i hi) q))
    hE hr hq hbalance


end CoarseDeGiorgi.LowerFractional
