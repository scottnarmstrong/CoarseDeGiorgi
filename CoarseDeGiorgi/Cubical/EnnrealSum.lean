module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Hölder and Minkowski for series of extended nonnegative numbers -/

@[expose] public section

namespace CoarseDeGiorgi.Cubical
open scoped BigOperators ENNReal
open Filter Topology

/-- Minkowski for finite sums of finitely many families. -/
theorem minkowski_fin {ι : Type*} (s : Finset ι) (f : ℕ → ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) (L : ℕ) :
    (∑ i ∈ s, (∑ l ∈ Finset.range L, f l i) ^ p) ^ (1 / p) ≤
      ∑ l ∈ Finset.range L, (∑ i ∈ s, f l i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  induction L with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [Finset.sum_eq_zero fun i _ => ENNReal.zero_rpow_of_pos hp0,
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)]
  | succ L ih =>
    simp only [Finset.sum_range_succ]
    calc (∑ i ∈ s, (∑ l ∈ Finset.range L, f l i + f L i) ^ p) ^ (1 / p)
        ≤ (∑ i ∈ s, (∑ l ∈ Finset.range L, f l i) ^ p) ^ (1 / p) +
            (∑ i ∈ s, f L i ^ p) ^ (1 / p) :=
          ENNReal.Lp_add_le s (fun i => ∑ l ∈ Finset.range L, f l i) (f L) hp
      _ ≤ _ := add_le_add ih le_rfl

/-- Minkowski for countable sums over `ℕ`. -/
theorem minkowski_tsum {ι : Type*} (s : Finset ι) (f : ℕ → ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, (∑' l, f l i) ^ p) ^ (1 / p) ≤ ∑' l, (∑ i ∈ s, f l i ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hlim : Tendsto (fun L => (∑ i ∈ s, (∑ l ∈ Finset.range L, f l i) ^ p) ^ (1 / p)) atTop
      (𝓝 ((∑ i ∈ s, (∑' l, f l i) ^ p) ^ (1 / p))) := by
    have h1 : ∀ i, Tendsto (fun L => ∑ l ∈ Finset.range L, f l i) atTop (𝓝 (∑' l, f l i)) :=
      fun i => ENNReal.tendsto_nat_tsum _
    have h2 : Tendsto (fun L => ∑ i ∈ s, (∑ l ∈ Finset.range L, f l i) ^ p) atTop
        (𝓝 (∑ i ∈ s, (∑' l, f l i) ^ p)) :=
      tendsto_finsetSum _ fun i _ => ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp (h1 i)
    exact ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto _).comp h2
  refine le_of_tendsto' hlim fun L => ?_
  exact (minkowski_fin s f hp L).trans (ENNReal.sum_le_tsum _)

/-- Weighted Hölder (Jensen) inequality for finite sums. -/
theorem holder_weighted {ι : Type*} (s : Finset ι) (c y : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, c i * y i) ^ p ≤ (∑ i ∈ s, c i) ^ (p - 1) * ∑ i ∈ s, c i * y i ^ p := by
  have hp0 : 0 < p := by linarith
  set C := ∑ i ∈ s, c i with hC
  by_cases hC0 : C = 0
  · have hc : ∀ i ∈ s, c i = 0 := (Finset.sum_eq_zero_iff.mp hC0)
    have : ∑ i ∈ s, c i * y i = 0 := Finset.sum_eq_zero fun i hi => by simp [hc i hi]
    rw [this, ENNReal.zero_rpow_of_pos hp0]; exact bot_le
  by_cases hCt : C = ⊤
  · rcases hp.eq_or_lt with h | h
    · subst h
      simp only [sub_self, ENNReal.rpow_zero, one_mul, ENNReal.rpow_one]
      exact le_of_eq (Finset.sum_congr rfl fun i _ => by simp)
    · have : (⊤ : ℝ≥0∞) ^ (p - 1) = ⊤ := ENNReal.top_rpow_of_pos (by linarith)
      rw [hCt, this]
      by_cases hz : ∑ i ∈ s, c i * y i ^ p = 0
      · -- then every c i * y i ^ p = 0, so y i = 0 whenever c i ≠ 0, and the left side vanishes
        have hz' : ∀ i ∈ s, c i * y i ^ p = 0 := Finset.sum_eq_zero_iff.mp hz
        have : ∑ i ∈ s, c i * y i = 0 := Finset.sum_eq_zero fun i hi => by
          have := hz' i hi
          rcases mul_eq_zero.mp this with h | h
          · simp [h]
          · have : y i = 0 := by
              by_contra hy
              rcases ENNReal.rpow_eq_zero_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
              · exact hy h1
              · linarith
            simp [this]
        rw [this, ENNReal.zero_rpow_of_pos hp0]; exact bot_le
      · rw [ENNReal.top_mul hz]; exact le_top
  · -- finite positive total weight
    set w : ι → ℝ≥0∞ := fun i => c i * C⁻¹ with hw
    have hw1 : ∑ i ∈ s, w i = 1 := by
      rw [← Finset.sum_mul]; exact ENNReal.mul_inv_cancel hC0 hCt
    have hj := ENNReal.rpow_arith_mean_le_arith_mean_rpow s w y hw1 hp
    have hCC : C * C⁻¹ = 1 := ENNReal.mul_inv_cancel hC0 hCt
    have e1 : ∑ i ∈ s, c i * y i = C * ∑ i ∈ s, w i * y i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      calc c i * y i = (C * C⁻¹) * (c i * y i) := by rw [hCC, one_mul]
        _ = _ := by simp only [hw]; ring
    have e2 : ∑ i ∈ s, c i * y i ^ p = C * ∑ i ∈ s, w i * y i ^ p := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      calc c i * y i ^ p = (C * C⁻¹) * (c i * y i ^ p) := by rw [hCC, one_mul]
        _ = _ := by simp only [hw]; ring
    have e3 : C ^ p = C ^ (p - 1) * C := by
      have := ENNReal.rpow_add (p - 1) 1 hC0 hCt
      rw [ENNReal.rpow_one] at this
      rw [← this]; congr 1; ring
    rw [e1, e2, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, e3]
    calc C ^ (p - 1) * C * (∑ i ∈ s, w i * y i) ^ p
        = C ^ (p - 1) * (C * (∑ i ∈ s, w i * y i) ^ p) := by ring
      _ ≤ C ^ (p - 1) * (C * ∑ i ∈ s, w i * y i ^ p) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hj)

/-- Assembly of the moment comparison, in extended nonnegative numbers. -/
theorem moment_assembly {τ : Type*} (s : Finset τ) {p : ℝ} (hp : 1 ≤ p) {N : ℝ≥0∞}
    (X : τ → ℝ≥0∞) (A B : ℕ → τ → ℝ≥0∞) (K Cube : ℕ → ℝ≥0∞)
    (hX : ∀ t, X t ≤ ∑' l, A l t)
    (hA : ∀ l t, A l t ^ p ≤ K l ^ (p - 1) * B l t)
    (hB : ∀ l, ∑ t ∈ s, B l t ≤ N * Cube l) (hN0 : N ≠ 0) (hNt : N ≠ ⊤) :
    ((∑ t ∈ s, X t ^ p) / N) ^ (1 / p) ≤ ∑' l, K l ^ (1 - 1 / p) * Cube l ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < 1 / p := one_div_pos.mpr hp0
  have h1 : (∑ t ∈ s, X t ^ p) ^ (1 / p) ≤ ∑' l, (∑ t ∈ s, A l t ^ p) ^ (1 / p) := by
    refine le_trans ?_ (minkowski_tsum s A hp)
    apply ENNReal.rpow_le_rpow _ hp1.le
    exact Finset.sum_le_sum fun t _ => ENNReal.rpow_le_rpow (hX t) hp0.le
  have h2 : ∀ l, (∑ t ∈ s, A l t ^ p) ^ (1 / p) ≤ N ^ (1 / p) * (K l ^ (1 - 1 / p) * Cube l ^ (1 / p)) := by
    intro l
    have : ∑ t ∈ s, A l t ^ p ≤ N * (K l ^ (p - 1) * Cube l) := by
      calc ∑ t ∈ s, A l t ^ p ≤ ∑ t ∈ s, K l ^ (p - 1) * B l t := Finset.sum_le_sum fun t _ => hA l t
        _ = K l ^ (p - 1) * ∑ t ∈ s, B l t := by rw [Finset.mul_sum]
        _ ≤ K l ^ (p - 1) * (N * Cube l) := mul_le_mul' le_rfl (hB l)
        _ = _ := by ring
    calc (∑ t ∈ s, A l t ^ p) ^ (1 / p) ≤ (N * (K l ^ (p - 1) * Cube l)) ^ (1 / p) :=
          ENNReal.rpow_le_rpow this hp1.le
      _ = N ^ (1 / p) * (K l ^ (1 - 1 / p) * Cube l ^ (1 / p)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp1.le, ENNReal.mul_rpow_of_nonneg _ _ hp1.le,
            ← ENNReal.rpow_mul]
          congr 3
          field_simp
  have hNp : N ^ (1 / p) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hN0) hNt).ne'
  have hNpt : N ^ (1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp1.le hNt
  rw [ENNReal.div_rpow_of_nonneg _ _ hp1.le, ENNReal.div_le_iff hNp hNpt]
  calc (∑ t ∈ s, X t ^ p) ^ (1 / p) ≤ ∑' l, (∑ t ∈ s, A l t ^ p) ^ (1 / p) := h1
    _ ≤ ∑' l, N ^ (1 / p) * (K l ^ (1 - 1 / p) * Cube l ^ (1 / p)) := ENNReal.tsum_le_tsum h2
    _ = _ := by rw [ENNReal.tsum_mul_left, mul_comm]

end CoarseDeGiorgi.Cubical
