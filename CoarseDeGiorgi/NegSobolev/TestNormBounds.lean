module

public import CoarseDeGiorgi.NegSobolev.TestNormTranslation
public import CoarseDeGiorgi.NegSobolev.TestNormArray
public import CoarseDeGiorgi.NegSobolev.TestNormRestriction

/-! Uniform integer and fractional bounds for the weak Gaussian derivative arrays. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

/-- Ordered weak derivatives of Gaussian averaging, with the tuple reversal
required by the integration-by-parts convention. -/
noncomputable def testNormGaussianArray {d : ℕ} (j : ℕ) (g : Vec d → ℝ)
    (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) (x : Vec d) : ℝ :=
  ∫ y, gaussDerivEntry t ht (fun k => ι k.rev) (x - y) * g y

theorem testNormGaussianArray_continuous {d : ℕ} (j : ℕ) (r : ℝ) (hr : 1 < r)
    (g : Vec d → ℝ) (hg : MemLp g (ENNReal.ofReal r) volume)
    (t : ℝ) (ht : 0 < t) (ι : Fin j → Fin d) :
    Continuous (testNormGaussianArray j g t ht ι) :=
  (testNorm_gaussDeriv_contDiff r hr g hg t ht _).continuous

theorem testNormGaussianArray_isWeakDerivArray {d : ℕ} (U : Set (Vec d))
    (j : ℕ) (r : ℝ) (hr : 1 < r) (g : Vec d → ℝ)
    (hg : MemLp g (ENNReal.ofReal r) volume) (t : ℝ) (ht : 0 < t) :
    IsWeakDerivArray U j (fun x => ∫ y, gaussianKernel t ht (x - y) * g y)
      (testNormGaussianArray j g t ht) := by
  have heq : (fun ι x => iteratedFDeriv ℝ j
      (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) x
        (fun k => basisVec (ι k.rev))) = testNormGaussianArray j g t ht := by
    funext ι x
    exact testNorm_gaussian_iteratedFDeriv r hr g hg t ht _ x
  rw [← heq]
  exact testNorm_isWeakDerivArray U j (testNorm_gaussian_contDiff r hr g hg t ht)

theorem testNormGaussianArray_eLpNorm_bound (d j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ) (_hr : 1 < r) (g : Vec d → ℝ),
      MemLp g (ENNReal.ofReal r) volume → ∀ (t : ℝ) (ht : 0 < t) (U : Set (Vec d)),
      eLpNorm (fun x => Real.sqrt (∑ ι, testNormGaussianArray j g t ht ι x ^ 2))
        (ENNReal.ofReal r) (volume.restrict U) ≤
          ENNReal.ofReal (C * t ^ (-((j : ℝ) / 2))) * eLpNorm g (ENNReal.ofReal r) volume := by
  obtain ⟨C, hC, hb⟩ := testNorm_gaussDeriv_eLpNorm_bound d j
  let N := Fintype.card (Fin j → Fin d)
  refine ⟨1 + N * C, by positivity, fun r hr g hg t ht U => ?_⟩
  have hmeas (ι : Fin j → Fin d) : Measurable (testNormGaussianArray j g t ht ι) :=
    (testNormGaussianArray_continuous j r hr g hg t ht ι).measurable
  refine (testNorm_eLpNorm_array_le_sum _ hmeas _ hr.le).trans ?_
  calc
    _ ≤ ∑ _ι : Fin j → Fin d,
        ENNReal.ofReal (C * t ^ (-((j : ℝ) / 2))) * eLpNorm g (ENNReal.ofReal r) volume :=
      Finset.sum_le_sum fun ι _ =>
        (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hb r hr g hg t ht _)
    _ = ENNReal.ofReal (N * (C * t ^ (-((j : ℝ) / 2)))) * eLpNorm g (ENNReal.ofReal r) volume := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, N,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (by
      have hp := Real.rpow_nonneg ht.le (-((j : ℝ) / 2))
      nlinarith)) le_rfl

theorem testNorm_arrayFracSeminorm_dimension_zero {ι : Type*} [Fintype ι]
    (U : Set (Vec 0)) (α r : ℝ) (hr : 0 < r) (F : ι → Vec 0 → ℝ) :
    arrayFracSeminorm U α r F = 0 := by
  unfold arrayFracSeminorm
  have hf : (fun p : Vec 0 × Vec 0 => ENNReal.ofReal
      ((Real.sqrt (∑ i, (F i p.1 - F i p.2) ^ 2)) ^ r /
        euclidDist p.1 p.2 ^ ((0 : ℝ) + α * r))) = 0 := by
    funext p
    rw [Subsingleton.elim p.1 p.2]
    simp [Real.zero_rpow hr.ne']
  simp only [Nat.cast_zero]
  rw [hf]
  change (∫⁻ _p : Vec 0 × Vec 0, (0 : ℝ≥0∞) ∂(volume.restrict U).prod (volume.restrict U)).rpow (1 / r) = 0
  rw [lintegral_zero]
  exact ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / r)

theorem testNormGaussianArray_fractional_bound (d j : ℕ) (α r : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : Vec d → ℝ), MemLp g (ENNReal.ofReal r) volume →
      ∀ (t : ℝ) (ht : 0 < t) (U : Set (Vec d)), MeasurableSet U →
      arrayFracSeminorm U α r (testNormGaussianArray j g t ht) ≤
        ENNReal.ofReal (C * t ^ (-(((j : ℝ) + α) / 2))) * eLpNorm g (ENNReal.ofReal r) volume := by
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, fun g hg t ht U _ => ?_⟩
    rw [testNorm_arrayFracSeminorm_dimension_zero U α r (zero_lt_one.trans hr)]
    exact bot_le
  · let : NeZero d := ⟨hd⟩
    obtain ⟨C, hC, hb⟩ := testNorm_gaussDeriv_translation_bound d j
    let R : ℝ := (∫ u : Vec d, Foundations.FracGeometry.cutoffRadial α r 1 u) ^ (1 / r)
    have hR : 0 ≤ R := Real.rpow_nonneg (integral_nonneg fun u =>
      Foundations.FracGeometry.cutoffRadial_nonneg α r zero_le_one u) _
    let N := Fintype.card (Fin j → Fin d)
    refine ⟨1 + R * (N * C), by positivity, fun g hg t ht U hU => ?_⟩
    have hm (ι : Fin j → Fin d) : Measurable (testNormGaussianArray j g t ht ι) :=
      (testNormGaussianArray_continuous j r hr g hg t ht ι).measurable
    have h := testNorm_arrayFracSeminorm_le_of_translation hα0 hα1 hr.le
      (Real.sqrt_pos.mpr ht) hU MeasurableSet.univ (Set.subset_univ U)
      (testNormGaussianArray j g t ht) hm
      (fun _ => ENNReal.ofReal (C * t ^ (-((j : ℝ) / 2))) * eLpNorm g (ENNReal.ofReal r) volume)
      (fun ι z => by simpa only [Measure.restrict_univ, testNormGaussianArray] using hb r hr g hg t ht (fun k => ι k.rev) z)
    have hpow : (Real.sqrt t) ^ (-α) * t ^ (-((j : ℝ) / 2)) =
        t ^ (-(((j : ℝ) + α) / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
      congr 1
      ring
    refine h.trans ?_
    change ENNReal.ofReal R * ENNReal.ofReal ((Real.sqrt t) ^ (-α)) * _ ≤ _
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (Fintype.card (Fin j → Fin d) : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) by simp [N]]
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hR,
      ← ENNReal.ofReal_mul (mul_nonneg hR (Real.rpow_nonneg (Real.sqrt_nonneg t) _)),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ R * (Real.sqrt t) ^ (-α) * (N : ℝ))]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have heq : R * (Real.sqrt t) ^ (-α) * (N : ℝ) * (C * t ^ (-((j : ℝ) / 2))) =
        (R * (N * C)) * t ^ (-(((j : ℝ) + α) / 2)) := by
      calc
        _ = R * (N * C) * ((Real.sqrt t) ^ (-α) * t ^ (-((j : ℝ) / 2))) := by ring
        _ = _ := by rw [hpow]
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (Real.rpow_nonneg ht.le _)

end CoarseDeGiorgi.NegSobolev
