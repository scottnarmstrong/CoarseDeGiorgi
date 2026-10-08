import CoarseDeGiorgi.Statements.ArrayFracSeminorm
import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyTranslation
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Component estimates for Euclidean derivative arrays and their fractional norms. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

private theorem array_length_le_sum_abs {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Real.sqrt (∑ i, a i ^ 2) ≤ ∑ i, |a i| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => |a i|) (fun i _ => abs_nonneg (a i))
  simp only [sq_abs] at hs
  exact (Real.sqrt_le_sqrt hs).trans_eq (Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _))

/-- A componentwise bound controls the Lebesgue norm of an array's Euclidean length. -/
theorem testNorm_eLpNorm_array_le_sum {X : Type*} [MeasurableSpace X]
    {ι : Type*} [Fintype ι] (F : ι → X → ℝ) (hF : ∀ i, Measurable (F i))
    (μ : Measure X) {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm (fun x => Real.sqrt (∑ i, F i x ^ 2)) (ENNReal.ofReal r) μ ≤
      ∑ i, eLpNorm (F i) (ENNReal.ofReal r) μ := by
  have hmeas : Measurable (fun x => Real.sqrt (∑ i, F i x ^ 2)) := by fun_prop
  calc
    _ ≤ eLpNorm (fun x => ∑ i, |F i x|) (ENNReal.ofReal r) μ :=
      eLpNorm_mono_real hmeas.aestronglyMeasurable (fun x =>
        by simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
          using array_length_le_sum_abs (fun i => F i x))
    _ ≤ ∑ i, eLpNorm (fun x => |F i x|) (ENNReal.ofReal r) μ := by
      have heq : (fun x => ∑ i, |F i x|) = ∑ i, fun x => |F i x| := by
        funext x
        simp only [Finset.sum_apply]
      rw [heq]
      exact (eLpNorm_sum_le (s := Finset.univ) (f := fun i x => |F i x|) (μ := μ)
          (by simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Real.norm_eq_abs] using eLpNorm_norm (F i) (hF i).aestronglyMeasurable

private theorem array_length_mul {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 ≤ c)
    (a : ι → ℝ) :
    Real.sqrt (∑ i, (c * a i) ^ 2) = c * Real.sqrt (∑ i, a i ^ 2) := by
  simp only [mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- The array seminorm is an ordinary Lebesgue norm on pairs, using the Euclidean
length of the componentwise difference quotients. -/
theorem testNorm_arrayFracSeminorm_eq_eLpNorm {d : ℕ} {ι : Type*} [Fintype ι]
    (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 0 < r)
    (F : ι → Vec d → ℝ) (hF : ∀ i, Measurable (F i)) :
    arrayFracSeminorm V α r F =
      eLpNorm (fun p => Real.sqrt (∑ i,
          Foundations.Reconstruction.assemblyQuotient α r (F i) p ^ 2))
        (ENNReal.ofReal r) ((volume.restrict V).prod (volume.restrict V)) := by
  have hQ (i : ι) := Foundations.Reconstruction.assemblyQuotient_measurable α r (hF i)
  have hmeas : Measurable (fun p : Vec d × Vec d => Real.sqrt (∑ i,
      Foundations.Reconstruction.assemblyQuotient α r (F i) p ^ 2)) := by
    fun_prop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top hmeas.aestronglyMeasurable, ENNReal.toReal_ofReal hr.le]
  unfold arrayFracSeminorm
  congr 1
  apply lintegral_congr
  intro p
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hr.le]
  unfold Foundations.Reconstruction.assemblyQuotient
  rw [array_length_mul _ (Real.rpow_nonneg (Foundations.Euclid.eDist2_nonneg _ _) _),
    Real.mul_rpow (Real.rpow_nonneg (Foundations.Euclid.eDist2_nonneg _ _) _) (Real.sqrt_nonneg _),
    ← Real.rpow_mul (Foundations.Euclid.eDist2_nonneg _ _)]
  have he : -(α + (d : ℝ) / r) * r = -((d : ℝ) + α * r) := by
    field_simp
    ring
  rw [he, Real.rpow_neg (Foundations.Euclid.eDist2_nonneg _ _),
    show euclidDist p.1 p.2 = Foundations.Euclid.eDist2 p.1 p.2 from rfl,
    div_eq_mul_inv, mul_comm]

/-- The fractional seminorm of a finite array is at most the sum of those of its
components. The constant is independent of the domain and of the array. -/
theorem testNorm_arrayFracSeminorm_le_sum {d : ℕ} {ι : Type*} [Fintype ι]
    (V : Set (Vec d)) (α : ℝ) {r : ℝ} (hr : 1 ≤ r)
    (F : ι → Vec d → ℝ) (hF : ∀ i, Measurable (F i)) :
    arrayFracSeminorm V α r F ≤ ∑ i, fracSeminorm V α r (F i) := by
  have hr0 := zero_lt_one.trans_le hr
  rw [testNorm_arrayFracSeminorm_eq_eLpNorm V α hr0 F hF]
  refine (testNorm_eLpNorm_array_le_sum
    (fun i => Foundations.Reconstruction.assemblyQuotient α r (F i))
    (fun i => Foundations.Reconstruction.assemblyQuotient_measurable α r (hF i))
    _ hr).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  exact (Foundations.Reconstruction.assembly_seminorm_eq_eLpNorm V α hr0 (hF i)).symm

/-- Radial integration converts translated component bounds to a fractional
array estimate. Its radial constant is selected independently of the scale. -/
theorem testNorm_arrayFracSeminorm_le_of_translation {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι] {α r h : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 ≤ r) (hh : 0 < h)
    {V B : Set (Vec d)} (hV : MeasurableSet V) (hB : MeasurableSet B) (hVB : V ⊆ B)
    (F : ι → Vec d → ℝ) (hF : ∀ i, Measurable (F i)) (M : ι → ℝ≥0∞)
    (htrans : ∀ i u, eLpNorm (fun x => F i (x + u) - F i x)
      (ENNReal.ofReal r) (volume.restrict B) ≤
        ENNReal.ofReal (min 1 (Foundations.Euclid.eNorm2 u / h)) * M i) :
    arrayFracSeminorm V α r F ≤
      ENNReal.ofReal ((∫ u : Vec d, Foundations.FracGeometry.cutoffRadial α r 1 u) ^ (1 / r)) *
        ENNReal.ofReal (h ^ (-α)) * ∑ i, M i := by
  refine (testNorm_arrayFracSeminorm_le_sum V α hr F hF).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact Foundations.Reconstruction.assembly_block_le hα0 hα1 (zero_lt_one.trans_le hr)
    hh hV hB hVB (hF i) (M i) (htrans i)

end CoarseDeGiorgi.NegSobolev
