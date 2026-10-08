import CoarseDeGiorgi.Foundations.FractionalSobolev.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The real dyadic weight, embedded in the extended nonnegative reals. -/
def sequenceWeight (T : ℝ) (k : ℤ) : ℝ≥0∞ := ENNReal.ofReal (T ^ (k : ℝ))

lemma sequenceWeight_ne_top (T : ℝ) (k : ℤ) : sequenceWeight T k ≠ ⊤ :=
  ENNReal.ofReal_ne_top

lemma sequenceWeight_add {T : ℝ} (hT : 0 < T) (i j : ℤ) :
    sequenceWeight T (i + j) = sequenceWeight T i * sequenceWeight T j := by
  simp only [sequenceWeight, Int.cast_add, Real.rpow_add hT,
    ENNReal.ofReal_mul (Real.rpow_pos_of_pos hT _).le]

lemma sequenceWeight_one {T : ℝ} : sequenceWeight T 1 = ENNReal.ofReal T := by
  simp [sequenceWeight]

lemma sequenceWeight_neg_nat {T : ℝ} (hT : 0 < T) (k : ℕ) :
    sequenceWeight T (-(k : ℤ)) = (ENNReal.ofReal T)⁻¹ ^ k := by
  simp only [sequenceWeight, Int.cast_neg, Int.cast_natCast]
  rw [Real.rpow_neg hT.le,
    Real.rpow_natCast, ENNReal.ofReal_inv_of_pos (pow_pos hT k)]
  rw [ENNReal.ofReal_pow hT.le, ENNReal.inv_pow]

/-- A sequence with a finite bound and an upper cutoff has finite weighted mass. -/
lemma weighted_tsum_ne_top {T α : ℝ} (hT : 1 < T) (hα : 0 < α)
    {a : ℤ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤) (ha : ∀ k, a k ≤ M)
    {N : ℤ} (hN : ∀ k, N ≤ k → a k = 0) :
    (∑' k, (a k) ^ α * sequenceWeight T k) ≠ ⊤ := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hshift := (Equiv.addRight N).tsum_eq (fun k : ℤ => (a k) ^ α * sequenceWeight T k)
  rw [← hshift, tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
  have hpos : (∑' k : ℕ, (a ((k : ℤ) + N)) ^ α * sequenceWeight T ((k : ℤ) + N)) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro k
    rw [hN _ (by omega), ENNReal.zero_rpow_of_pos hα, zero_mul]
  change (∑' k : ℕ, (a ((k : ℤ) + N)) ^ α * sequenceWeight T ((k : ℤ) + N)) +
    (∑' k : ℕ, (a (-((k : ℤ) + 1) + N)) ^ α *
      sequenceWeight T (-((k : ℤ) + 1) + N)) ≠ ⊤
  rw [hpos, zero_add]
  have hbound : (∑' k : ℕ, (a (-((k : ℤ) + 1) + N)) ^ α *
      sequenceWeight T (-((k : ℤ) + 1) + N)) ≤
      M ^ α * sequenceWeight T N * ∑' k : ℕ, (ENNReal.ofReal T)⁻¹ ^ (k + 1) := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro k
    rw [sequenceWeight_add hT0, mul_assoc, mul_comm (sequenceWeight T (-((k : ℤ) + 1))),
      ← mul_assoc]
    have hw := sequenceWeight_neg_nat hT0 (k + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hw
    rw [hw]
    simpa only [mul_assoc] using
      (mul_le_mul' (ENNReal.rpow_le_rpow (ha (-((k : ℤ) + 1) + N)) hα.le)
        (le_rfl : sequenceWeight T N * (ENNReal.ofReal T)⁻¹ ^ (k + 1) ≤
          sequenceWeight T N * (ENNReal.ofReal T)⁻¹ ^ (k + 1)))
  apply ne_top_of_le_ne_top _ hbound
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hα.le hM)
      (sequenceWeight_ne_top _ _)
  · have hr : (ENNReal.ofReal T)⁻¹ < 1 := by
      rw [ENNReal.inv_lt_one]
      exact ENNReal.one_lt_ofReal.mpr hT
    have hgeom : (∑' k : ℕ, (ENNReal.ofReal T)⁻¹ ^ k) ≠ ⊤ := by
      rw [ENNReal.tsum_geometric]
      exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hr))
    apply ne_top_of_le_ne_top hgeom
    exact ENNReal.tsum_le_tsum fun k => by rw [pow_succ]; exact mul_le_of_le_one_right' hr.le

/-- The zero-safe product identity used in the Hölder argument. -/
lemma sequence_holder_term {α θ : ℝ} (hα : 0 < α) (hθ : 0 < θ)
    (hsum : α + θ = 1) {x y w : ℝ≥0∞} (hx : x ≠ ⊤) (hyx : y ≤ x)
    (_hw : w ≠ ⊤) :
    (x ^ α * w) ^ θ * (y * x ^ (-θ) * w) ^ α = y ^ α * w := by
  by_cases hx0 : x = 0
  · have hy0 : y = 0 := le_zero_iff.mp (hx0 ▸ hyx)
    simp [hx0, hy0, ENNReal.zero_rpow_of_pos hα, ENNReal.zero_rpow_of_pos hθ]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le,
    ENNReal.mul_rpow_of_nonneg _ _ hα.le,
    ENNReal.mul_rpow_of_nonneg _ _ hα.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  calc
    x ^ (α * θ) * w ^ θ * (y ^ α * x ^ (-θ * α) * w ^ α) =
        y ^ α * (x ^ (α * θ) * x ^ (-θ * α)) * (w ^ θ * w ^ α) := by ac_rfl
    _ = y ^ α * w := by
      rw [← ENNReal.rpow_add _ _ hx0 hx, ← ENNReal.rpow_add_of_nonneg _ _ hθ.le hα.le]
      have hz : α * θ + -θ * α = 0 := by ring
      rw [hz, ENNReal.rpow_zero, mul_one, show θ + α = 1 by linarith,
        ENNReal.rpow_one]

/-- DNPV Lemma 6.2, with zero terms retained using ENNReal multiplication. -/
theorem lemma_6_2 {T θ : ℝ} (hT : 1 < T) (hθ : 0 < θ) (hθ1 : θ < 1)
    {a : ℤ → ℝ≥0∞} (ha : Antitone a)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hab : ∀ k, a k ≤ M)
    {N : ℤ} (hN : ∀ k, N ≤ k → a k = 0) :
    (∑' k, (a k) ^ (1 - θ) * sequenceWeight T k) ≤
      (ENNReal.ofReal T) ^ (1 / (1 - θ)) *
        ∑' k, a (k + 1) * (a k) ^ (-θ) * sequenceWeight T k := by
  let α := 1 - θ
  have hα : 0 < α := sub_pos.mpr hθ1
  have hsum : α + θ = 1 := by dsimp [α]; ring
  let H := ∑' k, (a k) ^ α * sequenceWeight T k
  let B := ∑' k, a (k + 1) * (a k) ^ (-θ) * sequenceWeight T k
  have hH : H ≠ ⊤ := weighted_tsum_ne_top hT hα hM hab hN
  have hax : ∀ k, a k ≠ ⊤ := fun k => ne_top_of_le_ne_top hM (hab k)
  have hh := ENNReal.lintegral_mul_norm_pow_le
    (μ := Measure.count)
    (f := fun k : ℤ => (a k) ^ α * sequenceWeight T k)
    (g := fun k : ℤ => a (k + 1) * (a k) ^ (-θ) * sequenceWeight T k)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
    hθ.le hα.le (by linarith : θ + α = 1)
  simp only [lintegral_count] at hh
  have hid : (∑' k : ℤ, ((a k) ^ α * sequenceWeight T k) ^ θ *
      (a (k + 1) * (a k) ^ (-θ) * sequenceWeight T k) ^ α) =
      H / ENNReal.ofReal T := by
    have hterm : ∀ k : ℤ, ((a k) ^ α * sequenceWeight T k) ^ θ *
        (a (k + 1) * (a k) ^ (-θ) * sequenceWeight T k) ^ α =
        (a (k + 1)) ^ α * sequenceWeight T k := fun k =>
      sequence_holder_term hα hθ hsum (hax k) (ha (by omega : k ≤ k + 1))
        (sequenceWeight_ne_top _ _)
    simp_rw [hterm]
    have hw : ∀ k : ℤ, sequenceWeight T k =
        sequenceWeight T (k + 1) / ENNReal.ofReal T := by
      intro k
      rw [sequenceWeight_add (lt_trans zero_lt_one hT), sequenceWeight_one,
        ENNReal.mul_div_cancel_right (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hT)))
          ENNReal.ofReal_ne_top]
    calc
      (∑' k : ℤ, (a (k + 1)) ^ α * sequenceWeight T k) =
          ∑' k : ℤ, ((a (k + 1)) ^ α * sequenceWeight T (k + 1)) / ENNReal.ofReal T := by
        apply tsum_congr; intro k; rw [hw k, ← mul_div_assoc]
      _ = H / ENNReal.ofReal T := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right]
        exact congrArg (fun z => z * (ENNReal.ofReal T)⁻¹)
          ((Equiv.addRight (1 : ℤ)).tsum_eq (fun k => (a k) ^ α * sequenceWeight T k))
  rw [hid] at hh
  change H / ENNReal.ofReal T ≤ H ^ θ * B ^ α at hh
  change H ≤ (ENNReal.ofReal T) ^ (1 / α) * B
  by_cases hH0 : H = 0
  · rw [hH0]; exact zero_le
  have hT0 : ENNReal.ofReal T ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hT))
  have hh' : H ≤ ENNReal.ofReal T * (H ^ θ * B ^ α) :=
    by simpa only [mul_comm] using (ENNReal.div_le_iff hT0 ENNReal.ofReal_ne_top).mp hh
  have hc : H ^ (-θ) * H ≤ H ^ (-θ) * (ENNReal.ofReal T * (H ^ θ * B ^ α)) :=
    mul_le_mul' le_rfl hh'
  have hcancel : H ^ (-θ) * H ^ θ = 1 := by
    rw [← ENNReal.rpow_add _ _ hH0 hH, neg_add_cancel, ENNReal.rpow_zero]
  have hleft : H ^ (-θ) * H = H ^ α := by
    calc
      _ = H ^ (-θ) * H ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = H ^ (-θ + 1) := (ENNReal.rpow_add _ _ hH0 hH).symm
      _ = _ := by congr 1; dsimp [α]; ring
  rw [hleft] at hc
  have hright : H ^ (-θ) * (ENNReal.ofReal T * (H ^ θ * B ^ α)) =
      ENNReal.ofReal T * B ^ α := by
    calc
      _ = ENNReal.ofReal T * (H ^ (-θ) * H ^ θ) * B ^ α := by ac_rfl
      _ = _ := by rw [hcancel, mul_one]
  rw [hright] at hc
  have hr := ENNReal.rpow_le_rpow hc (by positivity : 0 ≤ 1 / α)
  rw [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / α),
    ← ENNReal.rpow_mul, mul_one_div_cancel hα.ne', ENNReal.rpow_one,
    ENNReal.rpow_one] at hr
  exact hr

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
