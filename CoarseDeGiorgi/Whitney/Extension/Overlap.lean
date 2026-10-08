module

public import Mathlib

@[expose] public section

namespace CoarseDeGiorgi.WhitneyExt

open MeasureTheory Set
open scoped ENNReal

theorem tsum_setLIntegral_le {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (S : ι → Set X)
    (hS : ∀ i, MeasurableSet (S i)) (N : ℕ)
    (hN : ∀ x, ∀ s : Finset ι, (∀ i ∈ s, x ∈ S i) → s.card ≤ N) (u : X → ℝ≥0∞) :
    ∑' i, ∫⁻ x in S i, u x ∂μ ≤ (N : ℝ≥0∞) * ∫⁻ x, u x ∂μ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hsum : ∀ s : Finset ι, ∑ i ∈ s, ∫⁻ x in S i, u x ∂μ
      ≤ ∫⁻ x, ∑ i ∈ s, (S i).indicator u x ∂μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      simp only [Finset.sum_insert hj]
      calc _ ≤ ∫⁻ x, (S j).indicator u x ∂μ + ∫⁻ x, ∑ i ∈ s, (S i).indicator u x ∂μ := by
            rw [lintegral_indicator (hS j)]
            exact add_le_add le_rfl ih
        _ ≤ _ := le_lintegral_add _ _
  refine (hsum s).trans ?_
  calc ∫⁻ x, ∑ i ∈ s, (S i).indicator u x ∂μ ≤ ∫⁻ x, (N : ℝ≥0∞) * u x ∂μ := by
        refine lintegral_mono fun x => ?_
        have h1 : ∑ i ∈ s, (S i).indicator u x = ∑ i ∈ s.filter (fun i => x ∈ S i), u x := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : x ∈ S i <;> simp [h]
        rw [h1, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_left (Nat.cast_le.2 (hN x (s.filter (fun i => x ∈ S i)) (fun i hi => (Finset.mem_filter.1 hi).2)))
          _
    _ = _ := lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N)

theorem tsum_rpow_le_rpow_tsum {ι : Type*} (a : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    ∑' i, a i ^ p ≤ (∑' i, a i) ^ p := by
  have h0 : 0 ≤ p - 1 := by linarith
  have hp' : p = 1 + (p - 1) := by ring
  calc ∑' i, a i ^ p ≤ ∑' i, a i * (∑' j, a j) ^ (p - 1) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        conv_lhs => rw [hp', ENNReal.rpow_add_of_nonneg _ _ zero_le_one h0, ENNReal.rpow_one]
        exact mul_le_mul_right (ENNReal.rpow_le_rpow (ENNReal.le_tsum i) h0) _
    _ = (∑' i, a i) ^ p := by
        rw [ENNReal.tsum_mul_right]
        conv_rhs => rw [hp', ENNReal.rpow_add_of_nonneg _ _ zero_le_one h0, ENNReal.rpow_one]

theorem card_le_of_lattice {d : ℕ} {s : ℝ} (hs : 0 < s) {R : ℝ} (_hR : 0 ≤ R) (y : Fin d → ℝ)
    (T : Finset (Fin d → ℤ)) (hT : ∀ m ∈ T, ∀ i, |(m i : ℝ) * s - y i| ≤ R) :
    T.card ≤ (2 * ⌈R / s⌉₊ + 1) ^ d := by
  set k : ℕ := ⌈R / s⌉₊ with hk
  have hkR : R / s ≤ k := Nat.le_ceil _
  have hsub : T ⊆ Fintype.piFinset (fun i => Finset.Icc (⌊y i / s⌋ - (k : ℤ)) (⌊y i / s⌋ + k)) := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    have h := abs_le.1 (hT m hm i)
    have h1 : (m i : ℝ) ≤ y i / s + k := by
      have : (m i : ℝ) * s ≤ y i + R := by linarith [h.2]
      have h2 : (m i : ℝ) ≤ (y i + R) / s := by rw [le_div_iff₀ hs]; exact this
      have : (y i + R) / s = y i / s + R / s := add_div _ _ _
      linarith
    have h3 : y i / s - k ≤ (m i : ℝ) := by
      have : y i - R ≤ (m i : ℝ) * s := by linarith [h.1]
      have h2 : (y i - R) / s ≤ (m i : ℝ) := by rw [div_le_iff₀ hs]; exact this
      have : (y i - R) / s = y i / s - R / s := sub_div _ _ _
      linarith
    have hf := Int.floor_le (y i / s)
    have hf' := Int.lt_floor_add_one (y i / s)
    rw [Finset.mem_Icc]
    constructor
    · have : ((⌊y i / s⌋ - k : ℤ) : ℝ) ≤ m i := by push_cast; linarith
      exact_mod_cast this
    · have : (m i : ℝ) < ((⌊y i / s⌋ + k + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_lt.1 this
      omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc]
  have : ∀ x : Fin d, (⌊y x / s⌋ + ↑k + 1 - (⌊y x / s⌋ - ↑k)).toNat = 2 * k + 1 := by
    intro x; omega
  simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact le_rfl

end CoarseDeGiorgi.WhitneyExt
