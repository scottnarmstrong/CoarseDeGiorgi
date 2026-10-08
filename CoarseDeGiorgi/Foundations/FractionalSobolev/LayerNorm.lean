module

public import CoarseDeGiorgi.Foundations.FractionalSobolev.Kernel
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

namespace CoarseDeGiorgi.Foundations.FractionalSobolev
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

lemma rpow_sum_le_sum_rpow {I : Type*} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (b : I → ℝ≥0∞) (F : Finset I) :
    (∑ i ∈ F, b i) ^ α ≤ ∑ i ∈ F, (b i) ^ α := by
  classical
  induction F using Finset.induction with
  | empty => simp [ENNReal.zero_rpow_of_pos hα]
  | insert i F hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hα.le hα1).trans (add_le_add le_rfl ih)

lemma rpow_tsum_le_tsum_rpow {I : Type*} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (b : I → ℝ≥0∞) : (∑' i, b i) ^ α ≤ ∑' i, (b i) ^ α := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  change (ENNReal.orderIsoRpow α hα) (⨆ F : Finset I, ∑ i ∈ F, b i) ≤ _
  rw [OrderIso.map_iSup]
  apply iSup_le
  intro F
  exact (rpow_sum_le_sum_rpow hα hα1 b F).trans (ENNReal.sum_le_tsum F)

lemma layer_lintegral_le {n : ℕ} {f : Vec n → ℝ} (hf : Measurable f)
    {q : ℝ} (hq : 0 < q) :
    (∫⁻ x, (ENNReal.ofReal |f x|) ^ q) ≤
      ∑' k : ℤ, sequenceWeight ((2 : ℝ) ^ q) (k + 1) * volume (dyadicLevel f k) := by
  classical
  have hpoint : ∀ x : Vec n, (ENNReal.ofReal |f x|) ^ q ≤
      ∑' k : ℤ, (dyadicLevel f k).indicator
        (fun _ => sequenceWeight ((2 : ℝ) ^ q) (k + 1)) x := by
    intro x
    by_cases hx : f x = 0
    · simp only [hx, abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hq]
      exact zero_le
    obtain ⟨k, hk⟩ := exists_dyadicBand hx
    apply le_trans _ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem (s := dyadicLevel f k) (a := x) (mem_dyadicBand.mp hk).1, ← dyadicHeight_rpow]
    rw [ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hx)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (abs_nonneg _) (mem_dyadicBand.mp hk).2 hq.le)
  calc
    _ ≤ ∫⁻ x, ∑' k : ℤ, (dyadicLevel f k).indicator
        (fun _ => sequenceWeight ((2 : ℝ) ^ q) (k + 1)) x := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_tsum]
      · apply tsum_congr
        intro k
        exact lintegral_indicator_const (dyadicLevel_measurable hf _) _
      · intro k
        exact (measurable_const.indicator (dyadicLevel_measurable hf _)).aemeasurable

lemma layer_norm_le {n : ℕ} {p q α : ℝ} (_hp : 0 < p) (hq : 0 < q)
    (hα : 0 < α) (hα1 : α ≤ 1) (hqp : q * α = p)
    {f : Vec n → ℝ} (hf : Measurable f) :
    (eLpNorm f (ENNReal.ofReal q) volume).rpow p ≤
      ENNReal.ofReal ((2 : ℝ) ^ p) *
        ∑' k : ℤ, (volume (dyadicLevel f k)) ^ α * sequenceWeight ((2 : ℝ) ^ p) k := by
  have hqE : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  have hexp : (1 / q) * p = α := by rw [← hqp]; field_simp
  change (eLpNorm f (ENNReal.ofReal q) volume) ^ p ≤ _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hqE ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq.le, ← ENNReal.rpow_mul, hexp]
  simp only [Real.enorm_eq_ofReal_abs]
  calc
    _ ≤ (∑' k : ℤ, sequenceWeight ((2 : ℝ) ^ q) (k + 1) * volume (dyadicLevel f k)) ^ α :=
      ENNReal.rpow_le_rpow (layer_lintegral_le hf hq) hα.le
    _ ≤ ∑' k : ℤ, (sequenceWeight ((2 : ℝ) ^ q) (k + 1) * volume (dyadicLevel f k)) ^ α :=
      rpow_tsum_le_tsum_rpow hα hα1 _
    _ = _ := by
      have hw : ∀ k : ℤ, (sequenceWeight ((2 : ℝ) ^ q) (k + 1) * volume (dyadicLevel f k)) ^ α =
          ENNReal.ofReal ((2 : ℝ) ^ p) * ((volume (dyadicLevel f k)) ^ α * sequenceWeight ((2 : ℝ) ^ p) k) := by
        intro k
        rw [ENNReal.mul_rpow_of_nonneg _ _ hα.le]
        have heq : (sequenceWeight ((2 : ℝ) ^ q) (k + 1)) ^ α =
            sequenceWeight ((2 : ℝ) ^ p) (k + 1) := by
          unfold sequenceWeight
          rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _)]
          congr 1
          rw [← Real.rpow_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) q).le,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← hqp]
          congr 1
          ring
        rw [heq, sequenceWeight_add (Real.rpow_pos_of_pos (by norm_num) p), sequenceWeight_one]
        ac_rfl
      simp_rw [hw]
      exact ENNReal.tsum_mul_left

end
end CoarseDeGiorgi.Foundations.FractionalSobolev
