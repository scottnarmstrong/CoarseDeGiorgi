import CoarseDeGiorgi.NegSobolev.GaussianContraction
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # The Lebesgue norm of a finite partition step function -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- At a point of one member of a disjoint family, only that indicator contributes. -/
theorem sum_indicator_eq_of_mem {α ι E : Type*} [Fintype ι] [AddCommMonoid E]
    (U : ι → Set α) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (a : ι → E) {x : α} {i : ι} (hx : x ∈ U i) :
    (∑ j, (U j).indicator (fun _ => a j) x) = a i := by
  classical
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    exact Set.disjoint_left.mp (hdisj hji) hj hx
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The `p`th power of a nonnegative partition step function has an exact indicator expansion. -/
theorem partition_step_enorm_rpow {α ι : Type*} [Fintype ι]
    (U : ι → Set α) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (p : ℝ) (hp : 0 < p) (x : α) :
    ‖∑ i, (U i).indicator (fun _ => a i) x‖ₑ ^ p =
      ∑ i, (U i).indicator (fun _ => (ENNReal.ofReal (a i)) ^ p) x := by
  classical
  by_cases hx : ∃ i, x ∈ U i
  · obtain ⟨i, hi⟩ := hx
    rw [sum_indicator_eq_of_mem U hdisj a hi,
      sum_indicator_eq_of_mem U hdisj (fun i => (ENNReal.ofReal (a i)) ^ p) hi,
      ← ofReal_norm, Real.norm_of_nonneg (ha i)]
  · push Not at hx
    simp only [Set.indicator_of_notMem (hx _), Finset.sum_const_zero, enorm_zero,
      ENNReal.zero_rpow_of_pos hp]

/-- The exact `Lᵖ` norm formula for a finite nonnegative partition step function. -/
theorem eLpNorm_partition_step {d : ℕ} {ι : Type*} [Fintype ι]
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (p : ℝ) (hp : 0 < p) :
    eLpNorm (fun x => ∑ i, (U i).indicator (fun _ => a i) x) (ENNReal.ofReal p) volume =
      (∑ i, volume (U i) * (ENNReal.ofReal (a i)) ^ p) ^ (1 / p) := by
  classical
  have hF : Measurable (fun x => ∑ i, (U i).indicator (fun _ => a i) x) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hU i))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hp))
    ENNReal.ofReal_ne_top hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  simp_rw [partition_step_enorm_rpow U hdisj a ha p hp]
  rw [lintegral_finsetSum _ (fun i _ => measurable_const.indicator (hU i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator (hU i), lintegral_const, Measure.restrict_apply_univ, mul_comm]

/-- A pointwise bound on every cell gives the lower `Lᵖ` comparison for the
associated partition step function. -/
theorem eLpNorm_partition_step_le {d : ℕ} {ι : Type*} [Fintype ι]
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (C : ℝ) (hC : 0 ≤ C)
    (H : Vec d → ℝ) (hH : ∀ x, 0 ≤ H x) (p : ℝ≥0∞)
    (hle : ∀ i, ∀ x ∈ U i, a i ≤ C * H x) :
    eLpNorm (fun x => ∑ i, (U i).indicator (fun _ => a i) x) p volume ≤
      ENNReal.ofReal C * eLpNorm H p volume := by
  classical
  have hF : Measurable (fun x => ∑ i, (U i).indicator (fun _ => a i) x) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hU i))
  have hF0 (x : Vec d) : 0 ≤ ∑ i, (U i).indicator (fun _ => a i) x :=
    Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => ha i) x)
  have hbound (x : Vec d) : (∑ i, (U i).indicator (fun _ => a i) x) ≤ C * H x := by
    by_cases hx : ∃ i, x ∈ U i
    · obtain ⟨i, hi⟩ := hx
      rw [sum_indicator_eq_of_mem U hdisj a hi]
      exact hle i x hi
    · push Not at hx
      simp only [Set.indicator_of_notMem (hx _), Finset.sum_const_zero]
      exact mul_nonneg hC (hH x)
  have hnorm : eLpNorm (fun x => C * H x) p volume = ENNReal.ofReal C * eLpNorm H p volume := by
    change eLpNorm (C • H) p volume = _
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg hC]
  rw [← hnorm]
  apply eLpNorm_mono hF.aestronglyMeasurable
  intro x
  rw [Real.norm_of_nonneg (hF0 x), Real.norm_of_nonneg (mul_nonneg hC (hH x))]
  exact hbound x

/-- For equal cell volumes `1/N`, the step-function norm is the arithmetic
`Lᵖ` mean appearing in `p.besov.averages`. -/
theorem eLpNorm_partition_step_equal_volume {d : ℕ} {ι : Type*} [Fintype ι]
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (N : ℝ) (hN : 0 < N) (hvol : ∀ i, (volume (U i)).toReal = N⁻¹)
    (hfin : ∀ i, volume (U i) ≠ ⊤) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (p : ℝ) (hp : 0 < p) :
    eLpNorm (fun x => ∑ i, (U i).indicator (fun _ => a i) x) (ENNReal.ofReal p) volume =
      (ENNReal.ofReal ((∑ i, Real.rpow (a i) p) / N)) ^ (1 / p) := by
  classical
  rw [eLpNorm_partition_step U hU hdisj a ha p hp]
  congr 1
  have hv (i : ι) : volume (U i) = ENNReal.ofReal N⁻¹ := by
    rw [← hvol i, ENNReal.ofReal_toReal (hfin i)]
  have hpows (i : ι) : (ENNReal.ofReal (a i)) ^ p = ENNReal.ofReal (Real.rpow (a i) p) :=
    ENNReal.ofReal_rpow_of_nonneg (ha i) hp.le
  simp_rw [hv, hpows]
  have hsum : (∑ i, ENNReal.ofReal (Real.rpow (a i) p)) =
      ENNReal.ofReal (∑ i, Real.rpow (a i) p) :=
    (ENNReal.ofReal_sum_of_nonneg (f := fun i => Real.rpow (a i) p)
      (fun i _ => Real.rpow_nonneg (ha i) p)).symm
  rw [← Finset.mul_sum, hsum, ← ENNReal.ofReal_mul (inv_nonneg.mpr hN.le)]
  congr 1
  rw [div_eq_mul_inv, mul_comm]

end CoarseDeGiorgi.NegSobolev
