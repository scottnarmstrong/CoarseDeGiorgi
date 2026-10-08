module

public import CoarseDeGiorgi.Foundations.Reconstruction.AssemblySeminorm
public import CoarseDeGiorgi.Foundations.FracGeometry.Cutoff
public import CoarseDeGiorgi.Foundations.FracGeometry.TranslationComparison

/-! # Euclidean block estimates from translated `L^r` bounds

The cutoff radial integral supplies the finite dimensional constant.
Its numerator uses `min 2` and therefore also bounds the same integral with `min 1`.
-/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
variable {d : ℕ}

/-- Difference coordinates followed by restriction to the larger integration box. -/
theorem assembly_pair_integral_le_translation {V B : Set (Vec d)}
    (hV : MeasurableSet V) (hB : MeasurableSet B) (hVB : V ⊆ B)
    (β r : ℝ) {f : Vec d → ℝ} (hf : Measurable f) :
    (∫⁻ p, Euclid.euclidKernel β r f p
      ∂((volume.restrict V).prod (volume.restrict V))) ≤
      ∫⁻ u, ENNReal.ofReal (Euclid.eNorm2 u ^ (-β)) *
        ∫⁻ x in B, ENNReal.ofReal (|f (x + u) - f x| ^ r) := by
  let H := (V ×ˢ V).indicator (Euclid.euclidKernel β r f)
  have hH : Measurable H :=
    (FracGeometry.measurable_euclidKernel β r hf).indicator (hV.prod hV)
  have hchange := (measurePreserving_prod_add_swap
    (volume : Measure (Vec d)) volume).lintegral_comp hH
  rw [Measure.prod_restrict, ← lintegral_indicator (hV.prod hV), ← hchange]
  have hpoint (p : Vec d × Vec d) : H (p.2, p.2 + p.1) ≤
      ENNReal.ofReal (Euclid.eNorm2 p.1 ^ (-β)) *
        B.indicator (fun x => ENNReal.ofReal (|f (x + p.1) - f x| ^ r)) p.2 := by
    by_cases hp : (p.2, p.2 + p.1) ∈ V ×ˢ V
    · have hb : p.2 ∈ B := hVB hp.1
      simp only [H, indicator_of_mem hp, indicator_of_mem hb]
      have hn : Euclid.eNorm2 (-p.1) = Euclid.eNorm2 p.1 := by
        simpa using Euclid.eNorm2_smul (-1) p.1
      unfold Euclid.euclidKernel Euclid.eDist2
      rw [show p.2 - (p.2 + p.1) = -p.1 by abel, hn, abs_sub_comm,
        div_eq_mul_inv, ← Real.rpow_neg (Euclid.eNorm2_nonneg _),
        ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _), mul_comm]
    · simp only [H, indicator_of_notMem hp]
      exact bot_le
  refine (lintegral_mono hpoint).trans_eq ?_
  rw [lintegral_prod]
  · apply lintegral_congr
    intro u
    change (∫⁻ x, ENNReal.ofReal (Euclid.eNorm2 u ^ (-β)) *
      B.indicator (fun x => ENNReal.ofReal (|f (x + u) - f x| ^ r)) x) = _
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator hB]
  · exact (((Euclid.continuous_eNorm2.measurable.comp measurable_fst).pow
      measurable_const).ennreal_ofReal.mul
      ((FracGeometry.measurable_translationDifference hf r).indicator
        (hB.preimage measurable_snd))).aemeasurable

/-- The powered block bound obtained from Step 7's translated norm estimate. -/
theorem assembly_block_power_le [NeZero d] {α r h : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hh : 0 < h)
    {V B : Set (Vec d)} (hV : MeasurableSet V) (hB : MeasurableSet B) (hVB : V ⊆ B)
    {f : Vec d → ℝ} (hf : Measurable f) (M : ℝ≥0∞)
    (htrans : ∀ u : Vec d,
      eLpNorm (fun x => f (x + u) - f x) (ENNReal.ofReal r) (volume.restrict B) ≤
        ENNReal.ofReal (min 1 (Euclid.eNorm2 u / h)) * M) :
    CoarseDeGiorgi.fracSeminorm V α r f ^ r ≤
      ENNReal.ofReal (h ^ (-α * r)) *
        ENNReal.ofReal (∫ u : Vec d, FracGeometry.cutoffRadial α r 1 u) * M ^ r := by
  have hp : CoarseDeGiorgi.fracSeminorm V α r f ^ r =
      ∫⁻ p, Euclid.euclidKernel ((d : ℝ) + α * r) r f p
        ∂((volume.restrict V).prod (volume.restrict V)) := by
    rw [← fracSeminorm_eq_statement, FracGeometry.fracSeminorm_eq_eFracSeminorm,
      Euclid.eFracSeminorm, ← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
  rw [hp]
  refine (assembly_pair_integral_le_translation hV hB hVB _ r hf).trans ?_
  have hinner (u : Vec d) :
      ENNReal.ofReal (Euclid.eNorm2 u ^ (-((d : ℝ) + α * r))) *
        (∫⁻ x in B, ENNReal.ofReal (|f (x + u) - f x| ^ r)) ≤
      ENNReal.ofReal (FracGeometry.cutoffRadial α r h u) * M ^ r := by
    have hm0 : 0 ≤ min 1 (Euclid.eNorm2 u / h) :=
      le_min zero_le_one (div_nonneg (Euclid.eNorm2_nonneg _) hh.le)
    have hmeas : Measurable (fun x => f (x + u) - f x) :=
      (hf.comp (measurable_id.add_const u)).sub hf
    rw [← FracGeometry.eLpNorm_ofReal_rpow hr hmeas]
    have ht := ENNReal.rpow_le_rpow (htrans u) hr.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,
      ENNReal.ofReal_rpow_of_nonneg hm0 hr.le] at ht
    refine (mul_le_mul_right ht _).trans ?_
    rw [← mul_assoc]
    apply mul_le_mul_left
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Euclid.eNorm2_nonneg _) _)]
    apply ENNReal.ofReal_le_ofReal
    unfold FracGeometry.cutoffRadial
    simp only [div_eq_mul_inv, ← Real.rpow_neg (Euclid.eNorm2_nonneg _)]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hm0 (min_le_min_right _ (by norm_num : (1 : ℝ) ≤ 2)) hr.le)
      (Real.rpow_nonneg (Euclid.eNorm2_nonneg _) _)
  refine (lintegral_mono hinner).trans_eq ?_
  rw [lintegral_mul_const _ (FracGeometry.measurable_cutoffRadial α r h).ennreal_ofReal,
    FracGeometry.lintegral_cutoffRadial hα0 hα1 hr hh]

/-- The Euclidean seminorm bound, with a finite radial constant selected before the scale. -/
theorem assembly_block_le [NeZero d] {α r h : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 0 < r) (hh : 0 < h)
    {V B : Set (Vec d)} (hV : MeasurableSet V) (hB : MeasurableSet B) (hVB : V ⊆ B)
    {f : Vec d → ℝ} (hf : Measurable f) (M : ℝ≥0∞)
    (htrans : ∀ u : Vec d,
      eLpNorm (fun x => f (x + u) - f x) (ENNReal.ofReal r) (volume.restrict B) ≤
        ENNReal.ofReal (min 1 (Euclid.eNorm2 u / h)) * M) :
    CoarseDeGiorgi.fracSeminorm V α r f ≤
      ENNReal.ofReal ((∫ u : Vec d, FracGeometry.cutoffRadial α r 1 u) ^ (1 / r)) *
        ENNReal.ofReal (h ^ (-α)) * M := by
  have hi0 : 0 ≤ ∫ u : Vec d, FracGeometry.cutoffRadial α r 1 u :=
    integral_nonneg fun u => FracGeometry.cutoffRadial_nonneg α r zero_le_one u
  have ht := ENNReal.rpow_le_rpow
    (assembly_block_power_le hα0 hα1 hr hh hV hB hVB hf M htrans) (one_div_nonneg.mpr hr.le)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr.le),
    ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hr.le),
    ← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hi0 (one_div_nonneg.mpr hr.le),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hh.le _) (one_div_nonneg.mpr hr.le),
    ← Real.rpow_mul hh.le] at ht
  have he : (-α * r) * (1 / r) = -α := by field_simp
  rw [he, mul_comm (ENNReal.ofReal (h ^ (-α)))] at ht
  exact ht

end
end CoarseDeGiorgi.Foundations.Reconstruction
