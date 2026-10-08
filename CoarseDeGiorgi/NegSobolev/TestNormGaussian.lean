module

public import CoarseDeGiorgi.NegSobolev.TestNormBounds
public import CoarseDeGiorgi.NegSobolev.TestNormSum
public import CoarseDeGiorgi.Statements.IsOpenOriginCube

/-! The Gaussian test-function estimate used in Appendix B, `l.negative.sobolev`. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace CoarseDeGiorgi.NegSobolev

theorem testNorm_gaussian_sobolev_bound (d : ℕ) (β r : ℝ) (hβ : 0 ≤ β) (hr : 1 < r) :
    ∃ H : ℝ, 0 < H ∧ ∀ (g : Vec d → ℝ), MemLp g (ENNReal.ofReal r) volume →
      ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 → ∀ (U : Set (Vec d)) (hU : IsOpen U),
      sobolevNorm U hU β r hβ hr.le
        (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) ≤
          ENNReal.ofReal H * ENNReal.ofReal (t ^ (-β / 2)) * eLpNorm g (ENNReal.ofReal r) volume := by
  classical
  have hentries (j : Fin (⌊β⌋₊ + 1)) := testNormGaussianArray_eLpNorm_bound d j
  choose C hC hb using hentries
  have hfrac : ∃ A : ℝ, 0 < A ∧ ∀ (g : Vec d → ℝ), MemLp g (ENNReal.ofReal r) volume →
      ∀ (t : ℝ) (ht : 0 < t) (U : Set (Vec d)), MeasurableSet U →
      (if β - ⌊β⌋₊ = 0 then 0 else
        arrayFracSeminorm U (β - ⌊β⌋₊) r (testNormGaussianArray ⌊β⌋₊ g t ht)) ≤
          ENNReal.ofReal A * ENNReal.ofReal (t ^ (-β / 2)) * eLpNorm g (ENNReal.ofReal r) volume := by
    by_cases hα : β - ⌊β⌋₊ = 0
    · refine ⟨1, zero_lt_one, fun g hg t ht U hU => ?_⟩
      rw [ite_eq_left hα]
      exact bot_le
    · have hα0 : 0 < β - ⌊β⌋₊ := lt_of_le_of_ne (Nat.zero_le_self_sub_floor hβ) (Ne.symm hα)
      obtain ⟨A, hA, hbound⟩ := testNormGaussianArray_fractional_bound d ⌊β⌋₊
        (β - ⌊β⌋₊) r hα0 (Nat.self_sub_floor_lt_one β) hr
      refine ⟨A, hA, fun g hg t ht U hU => ?_⟩
      rw [ite_eq_right hα]
      have h := hbound g hg t ht U hU
      rw [show (⌊β⌋₊ : ℝ) + (β - ⌊β⌋₊) = β by ring,
        ← neg_div, ENNReal.ofReal_mul hA.le] at h
      exact h
  obtain ⟨A, hA, hfrac⟩ := hfrac
  refine ⟨(∑ j, C j) + A, add_pos_of_nonneg_of_pos
    (Finset.sum_nonneg fun j _ => (hC j).le) hA, fun g hg t ht ht1 U hU => ?_⟩
  let D : (j : Fin (⌊β⌋₊ + 1)) → (Fin j → Fin d) → Vec d → ℝ :=
    fun j => testNormGaussianArray j g t ht
  have hD (j : Fin (⌊β⌋₊ + 1)) : IsWeakDerivArray U j
      (fun x => ∫ y, gaussianKernel t ht (x - y) * g y) (D j) :=
    testNormGaussianArray_isWeakDerivArray U j r hr g hg t ht
  refine (testNorm_sobolevNorm_le_sum hU hβ hr.le D hD).trans ?_
  have hj (j : Fin (⌊β⌋₊ + 1)) : (j : ℝ) ≤ β :=
    (Nat.cast_le.mpr (Nat.le_of_lt_succ j.isLt)).trans (Nat.floor_le hβ)
  have hnorm (j : Fin (⌊β⌋₊ + 1)) :
      eLpNorm (fun x => Real.sqrt (∑ ι, D j ι x ^ 2)) (ENNReal.ofReal r) (volume.restrict U) ≤
        ENNReal.ofReal (C j) * ENNReal.ofReal (t ^ (-β / 2)) * eLpNorm g (ENNReal.ofReal r) volume := by
    refine (hb j r hr g hg t ht U).trans ?_
    rw [ENNReal.ofReal_mul (hC j).le]
    apply mul_le_mul' _ le_rfl
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith [hj j])
  have hf := hfrac g hg t ht U hU.measurableSet
  change (if β - ⌊β⌋₊ = 0 then 0 else
    arrayFracSeminorm U (β - ⌊β⌋₊) r (D (Fin.last ⌊β⌋₊))) ≤ _ at hf
  refine (add_le_add (Finset.sum_le_sum fun j _ => hnorm j) hf).trans_eq ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← add_mul,
    ← ENNReal.ofReal_sum_of_nonneg (fun j _ => (hC j).le),
    ← ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => (hC j).le) hA.le]

/-- Gaussian averaging supplies the bounded Sobolev test functions required by
the negative Sobolev estimate, uniformly over all finite-exponent inputs. -/
theorem gaussian_test_sobolev_bound :
    ∀ (d : ℕ) (β r : ℝ) (hβ : 0 ≤ β) (hr : 1 < r),
      ∃ H : ℝ, 0 < H ∧ ∀ (g : Vec d → ℝ), MemLp g (ENNReal.ofReal r) volume →
        ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 →
          MemLp (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ⊤
            (volume.restrict (originCube 1)) ∧
          sobolevNorm (originCube 1) (isOpen_originCube 1) β r hβ hr.le
            (fun x => ∫ y, gaussianKernel t ht (x - y) * g y ∂volume) ≤
              ENNReal.ofReal H * ENNReal.ofReal (Real.rpow t (-β / 2)) *
                eLpNorm g (ENNReal.ofReal r) volume := by
  intro d β r hβ hr
  obtain ⟨H, hH, hbound⟩ := testNorm_gaussian_sobolev_bound d β r hβ hr
  refine ⟨H, hH, fun g hg t ht ht1 => ⟨?_, hbound g hg t ht ht1 _ _⟩⟩
  have hc := testNorm_gaussian_memLp r hr.le g hg t ht
  obtain ⟨B, hB⟩ := testNorm_gaussian_bounded r hr g hg t ht
  exact memLp_top_of_bound (hc.aestronglyMeasurable.mono_measure Measure.restrict_le_self) B
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

end CoarseDeGiorgi.NegSobolev
