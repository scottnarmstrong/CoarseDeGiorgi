module

public import Mathlib.Analysis.MeanInequalities

/-! # Normalized finite power means for response comparisons -/

@[expose] public section

open scoped BigOperators

namespace CoarseDeGiorgi.SharpnessExamples

/-- The normalized v-mean on a finite set of cells. -/
noncomputable def finitePowerMean {ι : Type*} [Fintype ι] (f : ι → ℝ) (v : ℝ) : ℝ :=
  Real.rpow ((∑ i, Real.rpow (f i) v) / (Fintype.card ι : ℝ)) (1 / v)

theorem finitePowerMean_nonneg {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (v : ℝ) : 0 ≤ finitePowerMean f v := by
  unfold finitePowerMean
  exact Real.rpow_nonneg (div_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) v) (Nat.cast_nonneg _)) _

theorem finitePowerMean_mono {ι : Type*} [Fintype ι]
    {f g : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (hfg : ∀ i, f i ≤ g i)
    {v : ℝ} (hv : 0 < v) : finitePowerMean f v ≤ finitePowerMean g v := by
  unfold finitePowerMean
  apply Real.rpow_le_rpow
    (div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) v) (Nat.cast_nonneg _))
    _ (by positivity)
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (hf i) (hfg i) hv.le) (Nat.cast_nonneg _)

theorem finitePowerMean_const {ι : Type*} [Fintype ι] [Nonempty ι]
    {c v : ℝ} (hc : 0 ≤ c) (hv : 0 < v) :
    finitePowerMean (fun _ : ι => c) v = c := by
  unfold finitePowerMean
  simp only [Real.rpow_eq_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  rw [mul_div_cancel_left₀ _ hcard, ← Real.rpow_mul hc, mul_one_div_cancel hv.ne', Real.rpow_one]

theorem finitePowerMean_smul {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {c v : ℝ} (hc : 0 ≤ c) (hv : 0 < v) :
    finitePowerMean (fun i => c * f i) v = c * finitePowerMean f v := by
  unfold finitePowerMean
  simp only [Real.rpow_eq_pow, Real.mul_rpow hc (hf _), ← Finset.mul_sum]
  rw [mul_div_assoc, Real.mul_rpow (Real.rpow_nonneg hc v)
    (div_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) v) (Nat.cast_nonneg _)),
    ← Real.rpow_mul hc, mul_one_div_cancel hv.ne', Real.rpow_one]

theorem finitePowerMean_add_le {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    {v : ℝ} (hv : 1 ≤ v) :
    finitePowerMean (fun i => f i + g i) v ≤ finitePowerMean f v + finitePowerMean g v := by
  have h := Real.Lp_add_le (Finset.univ : Finset ι) f g hv
  simp only [abs_of_nonneg (hf _), abs_of_nonneg (hg _),
    abs_of_nonneg (add_nonneg (hf _) (hg _))] at h
  unfold finitePowerMean
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (add_nonneg (hf i) (hg i)) v)
    (Nat.cast_nonneg _) (1 / v),
    Real.div_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hf i) v)
      (Nat.cast_nonneg _) (1 / v),
    Real.div_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hg i) v)
      (Nat.cast_nonneg _) (1 / v), ← add_div]
  exact div_le_div_of_nonneg_right h (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end CoarseDeGiorgi.SharpnessExamples
