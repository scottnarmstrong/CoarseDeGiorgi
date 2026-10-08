import CoarseDeGiorgi.Selection.SamplingSeries

namespace CoarseDeGiorgi.Selection

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Source sampling discount, with the surface dimension `d-1`. -/
def triadicSamplingDiscount (d : ℕ) (s p : ℝ) (k : ℕ) : ℝ≥0∞ :=
  (3 : ℝ≥0∞) ^ (-((k : ℝ) * (s + ((d : ℝ) - 1) / (2 * p))))

/-- Pure scale cancellation: the price of sampling a layer cancels the cell-count growth. -/
theorem triadic_layer_identity (d : ℕ) (s : ℝ) {p : ℝ} (hp : 0 < p) (k : ℕ)
    (W total N : ℝ≥0∞) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤) :
    triadicSamplingDiscount d s p k * (W * (3 : ℝ≥0∞) ^ (-(k : ℝ)) * total) ^ (1 / (2 * p)) =
      (W * N) ^ (1 / (2 * p)) * (3 : ℝ≥0∞) ^ (-((k : ℝ) * s)) *
        (total / (N * (3 : ℝ≥0∞) ^ ((k : ℝ) * d))) ^ (1 / (2 * p)) := by
  have h30 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
  have h3top : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hcount0 : N * (3 : ℝ≥0∞) ^ ((k : ℝ) * d) ≠ 0 :=
    mul_ne_zero hN0 (by simp [ENNReal.rpow_eq_zero_iff, h30, h3top])
  have hcounttop : N * (3 : ℝ≥0∞) ^ ((k : ℝ) * d) ≠ ⊤ :=
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hNtop)
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero h30 h3top))).ne
  let avg := total / (N * (3 : ℝ≥0∞) ^ ((k : ℝ) * d))
  have ht : total = (N * (3 : ℝ≥0∞) ^ ((k : ℝ) * d)) * avg :=
    (ENNReal.mul_div_cancel hcount0 hcounttop).symm
  have he : W * (3 : ℝ≥0∞) ^ (-(k : ℝ)) * total =
      (W * N) * (3 : ℝ≥0∞) ^ (- (k : ℝ) + (k : ℝ) * d) * avg := by
    conv_lhs => rw [ht]
    rw [ENNReal.rpow_add _ _ h30 h3top]
    ring
  rw [he]
  have hr : 0 ≤ 1 / (2 * p) := by positivity
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ENNReal.mul_rpow_of_nonneg _ _ hr,
    ← ENNReal.rpow_mul]
  unfold triadicSamplingDiscount
  have hexp : -((k : ℝ) * (s + ((d : ℝ) - 1) / (2 * p))) +
      (- (k : ℝ) + (k : ℝ) * d) * (1 / (2 * p)) = -((k : ℝ) * s) := by ring
  calc
    _ = (W * N) ^ (1 / (2 * p)) *
        ((3 : ℝ≥0∞) ^ (-((k : ℝ) * (s + ((d : ℝ) - 1) / (2 * p)))) *
          (3 : ℝ≥0∞) ^ ((- (k : ℝ) + (k : ℝ) * d) * (1 / (2 * p)))) *
        avg ^ (1 / (2 * p)) := by ring
    _ = _ := by rw [← ENNReal.rpow_add _ _ h30 h3top, hexp]

/-- The full response sampling estimate, with the moment supplied through its exact identity.
`N` is the number of unit-cube simplices per grid cube (`d!` in the source). All response
data are abstract nonnegative weights. There is no assumed response-bound theorem. -/
theorem response_sampling_of_moment_identity {Cell : ℕ → Type*}
    (cells : ∀ k, Finset (Cell k)) (weight : ∀ k, Cell k → ℝ≥0∞)
    (incidence : ∀ k, Cell k → Set ℝ)
    (hinc : ∀ k c, c ∈ cells k → MeasurableSet (incidence k c))
    (d : ℕ) {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) (μ : Measure ℝ)
    (W N M : ℝ≥0∞) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hwidth : ∀ k c, c ∈ cells k → μ (incidence k c) ≤ W * (3 : ℝ≥0∞) ^ (-(k : ℝ)))
    (hmoment : M = (ENNReal.ofReal (1 - Real.rpow 3 (-s)) *
      ∑' k : ℕ, (3 : ℝ≥0∞) ^ (-((k : ℝ) * s)) *
        ((∑ c ∈ cells k, (weight k c) ^ p) / (N * (3 : ℝ≥0∞) ^ ((k : ℝ) * d))) ^
          (1 / (2 * p))) ^ (2 : ℕ)) :
    powerNorm (2 * p) μ (sampledSeries cells weight incidence (triadicSamplingDiscount d s p)) ≤
      (W * N) ^ (1 / (2 * p)) * M ^ (1 / 2 : ℝ) /
        ENNReal.ofReal (1 - Real.rpow 3 (-s)) := by
  have hp' : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq : 0 < 1 - Real.rpow 3 (-s) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs))
  have hb := sampledSeries_bound_of_incidence_width cells weight incidence
    (triadicSamplingDiscount d s p) (fun k => W * (3 : ℝ≥0∞) ^ (-(k : ℝ))) hinc hp μ hwidth
  simp_rw [triadic_layer_identity d s hp' _ W _ N hN0 hNtop, mul_assoc] at hb
  rw [ENNReal.tsum_mul_left] at hb
  apply hb.trans_eq
  rw [hmoment, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num
  let q := ENNReal.ofReal (1 - Real.rpow 3 (-s))
  have hcancel (a b : ℝ≥0∞) : a * (q * b) / q = a * b := by
    rw [mul_div_assoc, mul_comm q b,
      ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top]
  exact (hcancel _ _).symm


end

end CoarseDeGiorgi.Selection
