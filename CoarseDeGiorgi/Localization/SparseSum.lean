module

public import CoarseDeGiorgi.Statements.FracNorm
public import CoarseDeGiorgi.Foundations.FracGeometry.Cutoff
public import CoarseDeGiorgi.Foundations.FracGeometry.Defs
public import CoarseDeGiorgi.Statements.SurfaceFracNorm
public import Mathlib.Analysis.MeanInequalities

/-! # Powered fractional norms of finite sums with bounded overlap -/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open CoarseDeGiorgi.Foundations
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι : Type*} {d : ℕ}

/-- The only cardinality loss is the number of nonzero summands. -/
theorem abs_sum_rpow_le_of_support_card {r : ℝ} (hr : 1 ≤ r)
    (S : Finset ι) (f : ι → ℝ) {M : ℕ}
    (hc : (S.filter fun i => f i ≠ 0).card ≤ M) :
    |∑ i ∈ S, f i| ^ r ≤ (M : ℝ) ^ (r - 1) * ∑ i ∈ S, |f i| ^ r := by
  let A := S.filter fun i => f i ≠ 0
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have he : ∑ i ∈ A, f i = ∑ i ∈ S, f i := by
    apply Finset.sum_subset hAS
    intro i hi hn
    have hz : f i = 0 := by
      by_contra hf
      exact hn (Finset.mem_filter.mpr ⟨hi, hf⟩)
    exact hz
  have hp : ∑ i ∈ A, |f i| ^ r = ∑ i ∈ S, |f i| ^ r := by
    apply Finset.sum_subset hAS
    intro i hi hn
    have hz : f i = 0 := by
      by_contra hf
      exact hn (Finset.mem_filter.mpr ⟨hi, hf⟩)
    rw [hz, abs_zero, Real.zero_rpow (by linarith only [hr] : r ≠ 0)]
  rw [← he]
  calc
    _ ≤ (∑ i ∈ A, |f i|) ^ r := Real.rpow_le_rpow (abs_nonneg _)
      (Finset.abs_sum_le_sum_abs _ _) (by linarith only [hr])
    _ ≤ (A.card : ℝ) ^ (r - 1) * ∑ i ∈ A, |f i| ^ r :=
      Real.rpow_sum_le_const_mul_sum_rpow A f hr
    _ ≤ (M : ℝ) ^ (r - 1) * ∑ i ∈ A, |f i| ^ r := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast hc) (sub_nonneg.mpr hr)
    _ = _ := by rw [hp]

/-- Restrict to the union of the two endpoint supports. -/
theorem card_filter_difference_le {S : Finset ι} {f : ι → Vec d → ℝ} {M : ℕ}
    (hM : ∀ x, (S.filter fun i => f i x ≠ 0).card ≤ M) (x y : Vec d) :
    (S.filter fun i => f i x - f i y ≠ 0).card ≤ 2 * M := by
  have hsub : (S.filter fun i => f i x - f i y ≠ 0) ⊆
      (S.filter fun i => f i x ≠ 0) ∪ (S.filter fun i => f i y ≠ 0) := by
    intro i hi
    obtain ⟨hiS, hine⟩ := Finset.mem_filter.mp hi
    by_cases hx : f i x = 0
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hiS, ?_⟩
      intro hy
      exact hine (by rw [hx, hy, sub_self])
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiS, hx⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by
    have hx := hM x
    have hy := hM y
    omega))

/-- The fractional kernel of a sparse sum is bounded pointwise. -/
theorem fracKernel_sum_le_of_overlap {r α : ℝ} (hr : 1 ≤ r) (S : Finset ι)
    (f : ι → Vec d → ℝ) {M : ℕ}
    (hM : ∀ x, (S.filter fun i => f i x ≠ 0).card ≤ M) (xy : Vec d × Vec d) :
    fracKernel α r (fun x => ∑ i ∈ S, f i x) xy ≤
      ENNReal.ofReal ((2 * M : ℕ) ^ (r - 1 : ℝ)) * ∑ i ∈ S, fracKernel α r (f i) xy := by
  have hh := abs_sum_rpow_le_of_support_card hr S
    (fun i => f i xy.1 - f i xy.2)
    (card_filter_difference_le hM xy.1 xy.2)
  rw [Finset.sum_sub_distrib] at hh
  unfold fracKernel fracKernelWithDimension
  have hd : 0 ≤ CoarseDeGiorgi.euclidDist xy.1 xy.2 ^ ((d : ℝ) + α * r) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hdiv := div_le_div_of_nonneg_right hh hd
  rw [mul_div_assoc, Finset.sum_div] at hdiv
  apply (ENNReal.ofReal_le_ofReal hdiv).trans_eq
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), ENNReal.ofReal_sum_of_nonneg]
  intro i _
  exact div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hd

/-- Powered Lebesgue norm as a nonnegative integral. -/
theorem lintegral_power_eq_eLpNorm_rpow {r : ℝ} (hr : 0 < r)
    {f : Vec d → ℝ} (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (|f x| ^ r)) = eLpNorm f (ENNReal.ofReal r) volume ^ r := by
  have hh := FracGeometry.lintegral_cutoffMass (V := (univ : Set (Vec d))) MeasurableSet.univ hr
    hf.aestronglyMeasurable.restrict
  simpa only [FracGeometry.cutoffMass, indicator_univ, Measure.restrict_univ] using hh

/-- The powered norm `fracNorm` unfolds without creating a second definition. -/
theorem statement_fracNorm_rpow (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ) :
    fracNorm V α r f ^ r = eLpNorm f (ENNReal.ofReal r) (volume.restrict V) ^ r +
      fracSeminorm V α r f ^ r := by
  exact FracGeometry.fracNorm_rpow V α hr f

/-- The raw integral underlying the powered seminorm `fracSeminorm`. -/
theorem statement_fracSeminorm_rpow (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ) : fracSeminorm V α r f ^ r =
      ∫⁻ xy, fracKernel α r f xy ∂((volume.restrict V).prod (volume.restrict V)) := by
  exact FracGeometry.fracSeminorm_rpow V α hr f

theorem measurable_fracKernel (α r : ℝ) {f : Vec d → ℝ} (hf : Measurable f) :
    Measurable (fracKernel α r f) := by
  change Measurable (Euclid.euclidKernel ((d : ℝ) + α * r) r f)
  simpa only [FracGeometry.cutoffInterior, indicator_univ, univ_prod_univ] using
    FracGeometry.measurable_cutoffInterior (V := (univ : Set (Vec d))) MeasurableSet.univ α r hf

/-- Norm assembly uses twice the overlap for pair differences, independent of #S. -/
theorem fracNorm_sum_rpow_le_of_overlap {r α : ℝ} (hr : 1 < r) (S : Finset ι)
    (f : ι → Vec d → ℝ) (hf : ∀ i ∈ S, Measurable (f i)) {M : ℕ}
    (hM : ∀ x, (S.filter fun i => f i x ≠ 0).card ≤ M) :
    fracNorm univ α r (fun x => ∑ i ∈ S, f i x) ^ r ≤
      ENNReal.ofReal ((2 * M : ℕ) ^ (r - 1 : ℝ)) * ∑ i ∈ S, fracNorm univ α r (f i) ^ r := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  let A : ℝ≥0∞ := ENNReal.ofReal ((2 * M : ℕ) ^ (r - 1 : ℝ))
  have hsum : Measurable (fun x => ∑ i ∈ S, f i x) := Finset.measurable_sum S hf
  have hLP : eLpNorm (fun x => ∑ i ∈ S, f i x) (ENNReal.ofReal r) volume ^ r ≤
      A * ∑ i ∈ S, eLpNorm (f i) (ENNReal.ofReal r) volume ^ r := by
    rw [← lintegral_power_eq_eLpNorm_rpow hr0 hsum]
    calc
      _ ≤ ∫⁻ x, A * ∑ i ∈ S, ENNReal.ofReal (|f i x| ^ r) := by
        apply lintegral_mono
        intro x
        have hh := abs_sum_rpow_le_of_support_card hr.le S (fun i => f i x)
          ((hM x).trans (by omega : M ≤ 2 * M))
        apply (ENNReal.ofReal_le_ofReal hh).trans_eq
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact Real.rpow_nonneg (abs_nonneg _) _
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum]
        · congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact lintegral_power_eq_eLpNorm_rpow hr0 (hf i hi)
        · intro i hi
          simpa only [Real.norm_eq_abs] using ((hf i hi).norm.pow measurable_const).ennreal_ofReal
  have hSem : fracSeminorm univ α r (fun x => ∑ i ∈ S, f i x) ^ r ≤
      A * ∑ i ∈ S, fracSeminorm univ α r (f i) ^ r := by
    rw [statement_fracSeminorm_rpow univ α hr0, Measure.restrict_univ]
    calc
      _ ≤ ∫⁻ xy, A * ∑ i ∈ S, fracKernel α r (f i) xy ∂volume.prod volume :=
        lintegral_mono (fracKernel_sum_le_of_overlap hr.le S f hM)
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum]
        · congr 1
          apply Finset.sum_congr rfl
          intro i _
          simpa only [Measure.restrict_univ] using (statement_fracSeminorm_rpow univ α hr0 (f i)).symm
        · intro i hi
          exact measurable_fracKernel α r (hf i hi)
  simp_rw [statement_fracNorm_rpow univ α hr0, Measure.restrict_univ, Finset.sum_add_distrib]
  rw [mul_add]
  exact add_le_add hLP hSem

end
end CoarseDeGiorgi.Localization
