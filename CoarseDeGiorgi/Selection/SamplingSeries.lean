import CoarseDeGiorgi.Selection.Sampling

namespace CoarseDeGiorgi.Selection

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

theorem powerNorm_const_mul {r : ℝ} (hr : 0 < r) (μ : Measure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (c : ℝ≥0∞) :
    powerNorm r μ (fun τ => c * f τ) = c * powerNorm r μ f := by
  unfold powerNorm
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
  rw [lintegral_const_mul _ (hf.pow_const r), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one]

/-- Minkowski for the nonnegative infinite series, proved by directed monotone convergence. -/
theorem powerNorm_tsum_le {r : ℝ} (hr : 1 ≤ r) (μ : Measure ℝ)
    (f : ℕ → ℝ → ℝ≥0∞) (hf : ∀ k, Measurable (f k)) :
    powerNorm r μ (fun τ => ∑' k, f k τ) ≤ ∑' k, powerNorm r μ (f k) := by
  have hr' : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hmeas (s : Finset ℕ) : Measurable (fun τ => (∑ k ∈ s, f k τ) ^ r) :=
    (Finset.measurable_sum _ (fun k _ => hf k)).pow_const r
  have hdir : Directed (· ≤ ·) (fun s : Finset ℕ => fun τ => (∑ k ∈ s, f k τ) ^ r) := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · intro τ; exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.subset_union_left)) hr'.le
    · intro τ; exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (Finset.subset_union_right)) hr'.le
  have heq : powerNorm r μ (fun τ => ∑' k, f k τ) =
      ⨆ s : Finset ℕ, powerNorm r μ (fun τ => ∑ k ∈ s, f k τ) := by
    unfold powerNorm
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    have hpow (τ : ℝ) : (⨆ s : Finset ℕ, ∑ k ∈ s, f k τ) ^ r =
        ⨆ s : Finset ℕ, (∑ k ∈ s, f k τ) ^ r :=
      (ENNReal.orderIsoRpow r hr').map_iSup _
    simp_rw [hpow]
    rw [lintegral_iSup_directed_of_measurable hmeas hdir]
    exact (ENNReal.orderIsoRpow (1 / r) (one_div_pos.mpr hr')).map_iSup _
  rw [heq]
  apply iSup_le
  intro s
  exact (powerNorm_sum_le s hr μ f (fun k _ => hf k)).trans (ENNReal.sum_le_tsum s)

/-- The discounted series of abstract sampled responses (`e.boundary.maxima.series`).
The caller supplies the discount `3^(-k(s+(d-1)/(2p)))` as `discount k`. -/
def sampledSeries {Cell : ℕ → Type*} (cells : ∀ k, Finset (Cell k))
    (weight : ∀ k, Cell k → ℝ≥0∞) (incidence : ∀ k, Cell k → Set ℝ)
    (discount : ℕ → ℝ≥0∞) (τ : ℝ) : ℝ≥0∞ :=
  ∑' k, discount k * (sampledMaximum (cells k) (weight k) (incidence k) τ) ^ (1 / 2 : ℝ)

theorem sampledSeries_measurable {Cell : ℕ → Type*} (cells : ∀ k, Finset (Cell k))
    (weight : ∀ k, Cell k → ℝ≥0∞) (incidence : ∀ k, Cell k → Set ℝ)
    (discount : ℕ → ℝ≥0∞) (hinc : ∀ k c, c ∈ cells k → MeasurableSet (incidence k c)) :
    Measurable (sampledSeries cells weight incidence discount) := by
  exact Measurable.tsum (fun k => measurable_const.mul
    ((sampledMaximum_measurable (cells k) (weight k) (incidence k) (hinc k)).pow_const _))

/-- Response sampling with explicit incidence widths and weights, before moment normalization.
No coefficient response or moment definition is imported. -/
theorem sampledSeries_bound_of_incidence_width {Cell : ℕ → Type*}
    (cells : ∀ k, Finset (Cell k)) (weight : ∀ k, Cell k → ℝ≥0∞)
    (incidence : ∀ k, Cell k → Set ℝ) (discount width : ℕ → ℝ≥0∞)
    (hinc : ∀ k c, c ∈ cells k → MeasurableSet (incidence k c))
    {p : ℝ} (hp : 1 ≤ p) (μ : Measure ℝ)
    (hwidth : ∀ k c, c ∈ cells k → μ (incidence k c) ≤ width k) :
    powerNorm (2 * p) μ (sampledSeries cells weight incidence discount) ≤
      ∑' k, discount k * (width k * ∑ c ∈ cells k, (weight k c) ^ p) ^ (1 / (2 * p)) := by
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h2p : 0 < 2 * p := by positivity
  apply (powerNorm_tsum_le (by linarith : 1 ≤ 2 * p) μ _
    (fun k => measurable_const.mul
      ((sampledMaximum_measurable (cells k) (weight k) (incidence k) (hinc k)).pow_const _))).trans
  apply ENNReal.tsum_le_tsum
  intro k
  change powerNorm (2 * p) μ (fun τ => discount k *
    (sampledMaximum (cells k) (weight k) (incidence k) τ) ^ (1 / 2 : ℝ)) ≤ _
  rw [powerNorm_const_mul h2p μ
    ((sampledMaximum_measurable (cells k) (weight k) (incidence k) (hinc k)).pow_const _)]
  apply mul_le_mul_right
  unfold powerNorm
  simp_rw [← ENNReal.rpow_mul]
  have he : (1 / 2 : ℝ) * (2 * p) = p := by ring
  rw [he]
  exact ENNReal.rpow_le_rpow (sampledMaximum_integral_le (cells k) (weight k) (incidence k)
    (hinc k) hp' (hwidth k)) (by positivity)


end

end CoarseDeGiorgi.Selection
