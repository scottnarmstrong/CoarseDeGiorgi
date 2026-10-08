module

public import CoarseDeGiorgi.Harnack.Calculus.EssentialValues
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- Uniform bounds for finite-exponent seminorms with exponents tending to
infinity imply the corresponding essential-supremum bound. The fixed factor
`K^(1/p)` allows the total mass of the measure to enter explicitly.
-/
theorem eLpNormEssSup_le_of_uniform_rpowLpBound
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [TopologicalSpace E] [ContinuousENorm E]
    {μ : Measure α} {f : α → E} {A K : ℝ≥0∞}
    (hμ : μ Set.univ ≠ ⊤)
    (hf : AEStronglyMeasurable f μ)
    (hApos : 0 < A) (hAtop : A ≠ ⊤)
    (hKpos : 0 < K) (hKtop : K ≠ ⊤)
    (p : ℕ → ℝ) (hp : ∀ n, 0 < p n)
    (hpTop : Tendsto p atTop atTop)
    (hbound : ∀ n,
      eLpNorm' f (p n) μ ≤ A * K ^ (1 / p n)) :
    eLpNormEssSup f μ ≤ A := by
  by_contra hnot
  have hAess : A < eLpNormEssSup f μ := lt_of_not_ge hnot
  have hAess' : A < essSup (fun x => ‖f x‖ₑ) μ := by
    simpa [eLpNormEssSup_eq_essSup_enorm] using hAess
  obtain ⟨L, hAL, hLess⟩ := exists_between hAess'
  have hLtop : L ≠ ⊤ := ne_of_lt (hLess.trans_le le_top)
  have hLpos : 0 < L := lt_trans hApos hAL
  have hLrealpos : 0 < L.toReal := ENNReal.toReal_pos hLpos.ne' hLtop
  have hArealpos : 0 < A.toReal := ENNReal.toReal_pos hApos.ne' hAtop
  have hArealLreal : A.toReal < L.toReal := by
    apply lt_of_not_ge
    intro h
    have hLA : L ≤ A := by
      calc
        L = ENNReal.ofReal L.toReal := (ENNReal.ofReal_toReal hLtop).symm
        _ ≤ ENNReal.ofReal A.toReal := ENNReal.ofReal_le_ofReal h
        _ = A := ENNReal.ofReal_toReal hAtop
    exact (not_le_of_gt hAL) hLA
  let S : Set α := {x | L < ‖f x‖ₑ}
  have hSpos : 0 < μ S := by
    apply (CoarseDeGiorgi.Harnack.Calculus.ennreal_lt_essSup_iff_measure_pos
      μ (fun x => ‖f x‖ₑ) L).mp
    simpa [S] using hLess
  have hSle : μ S ≤ μ Set.univ := measure_mono (Set.subset_univ S)
  have hStop : μ S ≠ ⊤ := ne_of_lt
    (lt_of_le_of_lt hSle (lt_top_iff_ne_top.mpr hμ))
  have hSrealpos : 0 < (μ S).toReal := ENNReal.toReal_pos hSpos.ne' hStop
  have hKrealpos : 0 < K.toReal := ENNReal.toReal_pos hKpos.ne' hKtop
  let q : ℝ := A.toReal / L.toReal
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact (div_lt_one hLrealpos).2 hArealLreal
  have hratioPos : 0 < (μ S).toReal / K.toReal := div_pos hSrealpos hKrealpos
  have hratio (n : ℕ) : (μ S).toReal / K.toReal ≤ q ^ (p n) := by
    let P : ℝ≥0∞ := ENNReal.ofReal (p n)
    have hPzero : P ≠ 0 := by
      dsimp [P]
      exact (ENNReal.ofReal_pos.mpr (hp n)).ne'
    have hPtop : P ≠ ⊤ := by dsimp [P]; exact ENNReal.ofReal_ne_top
    have hPtoReal : P.toReal = p n := by
      dsimp [P]
      exact ENNReal.toReal_ofReal (hp n).le
    have hKpow : (K ^ (1 / p n)) ^ (p n) = K := by
      rw [← ENNReal.rpow_mul]
      rw [one_div, inv_mul_cancel₀ (ne_of_gt (hp n)), ENNReal.rpow_one]
    have hboundPow : eLpNorm' f (p n) μ ^ (p n) ≤ A ^ (p n) * K := by
      have h := ENNReal.rpow_le_rpow (hbound n) (le_of_lt (hp n))
      rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt (hp n)), hKpow] at h
      exact h
    have hMarkov := MeasureTheory.mul_meas_ge_le_pow_eLpNorm' μ
      hPzero hPtop (f := f) L
    have hMarkov' : L ^ (p n) * μ {x | L ≤ ‖f x‖ₑ} ≤
        eLpNorm' f (p n) μ ^ (p n) := by
      simpa only [hPtoReal, eLpNorm_eq_eLpNorm' hPzero hPtop hf] using hMarkov
    have hSsub : S ⊆ {x | L ≤ ‖f x‖ₑ} := by
      intro x hx
      change L < ‖f x‖ₑ at hx
      exact le_of_lt hx
    have hmarkS : L ^ (p n) * μ S ≤ eLpNorm' f (p n) μ ^ (p n) := by
      calc
        L ^ (p n) * μ S ≤
            L ^ (p n) * μ {x | L ≤ ‖f x‖ₑ} :=
          mul_le_mul_of_nonneg_left (measure_mono hSsub)
            zero_le
        _ ≤ eLpNorm' f (p n) μ ^ (p n) := hMarkov'
    have hfull : L ^ (p n) * μ S ≤ A ^ (p n) * K := hmarkS.trans hboundPow
    have hfullTop : A ^ (p n) * K ≠ ⊤ := by finiteness
    have hreal := ENNReal.toReal_mono hfullTop hfull
    have hreal' : L.toReal ^ (p n) * (μ S).toReal ≤
        A.toReal ^ (p n) * K.toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow] using hreal
    have hLpowPos : 0 < L.toReal ^ (p n) := Real.rpow_pos_of_pos hLrealpos _
    have hdenPos : 0 < L.toReal ^ (p n) * K.toReal := mul_pos hLpowPos hKrealpos
    have hdiv := div_le_div_of_nonneg_right hreal' hdenPos.le
    have hleft :
        (L.toReal ^ (p n) * (μ S).toReal) /
            (L.toReal ^ (p n) * K.toReal) = (μ S).toReal / K.toReal := by
      field_simp
    have hright :
        (A.toReal ^ (p n) * K.toReal) /
            (L.toReal ^ (p n) * K.toReal) =
          A.toReal ^ (p n) / L.toReal ^ (p n) := by
      field_simp
    have hratioPow : (μ S).toReal / K.toReal ≤
        A.toReal ^ (p n) / L.toReal ^ (p n) := by
      rw [← hleft, ← hright]
      exact hdiv
    calc
      (μ S).toReal / K.toReal ≤ A.toReal ^ (p n) / L.toReal ^ (p n) := hratioPow
      _ = (A.toReal / L.toReal) ^ (p n) := by
        symm
        exact Real.div_rpow hArealpos.le hLrealpos.le (p n)
      _ = q ^ (p n) := by rfl
  have hqpow : Tendsto (fun n : ℕ => q ^ (p n)) atTop (nhds 0) :=
    (tendsto_rpow_atTop_of_base_lt_one q (by linarith) hq1).comp hpTop
  have hlim : (μ S).toReal / K.toReal ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hqpow hratio
  exact (not_le_of_gt hratioPos) hlim

/-- For an a.e.-positive function, a reciprocal essential-supremum estimate is
the corresponding lower bound for the nonnegative essential infimum `nonnegativeEssInf`.
-/
theorem nonnegativeEssInf_ge_inv_of_reciprocal_essSup_bound {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) (A : ℝ≥0∞)
    (hu : ∀ᵐ x ∂(volume.restrict V), 0 < u x)
    (hbound : eLpNormEssSup (fun x => (u x)⁻¹) (volume.restrict V) ≤ A) :
    A⁻¹ ≤ CoarseDeGiorgi.nonnegativeEssInf V u := by
  let μ := volume.restrict V
  have hnorm :
      (fun x => ‖(u x)⁻¹‖ₑ) =ᵐ[μ]
        (fun x => (ENNReal.ofReal (u x))⁻¹) := by
    filter_upwards [hu] with x hx
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (inv_nonneg.mpr hx.le),
      ENNReal.ofReal_inv_of_pos hx]
  have hess : essSup (fun x => (ENNReal.ofReal (u x))⁻¹) μ ≤ A := by
    calc
      essSup (fun x => (ENNReal.ofReal (u x))⁻¹) μ =
          essSup (fun x => ‖(u x)⁻¹‖ₑ) μ := essSup_congr_ae hnorm.symm
      _ = eLpNormEssSup (fun x => (u x)⁻¹) μ := rfl
      _ ≤ A := hbound
  have hinv :
      (essInf (fun x => ENNReal.ofReal (u x)) μ)⁻¹ ≤ A := by
    simpa only [CoarseDeGiorgi.Harnack.Calculus.essSup_inv_eq_inv_essInf]
      using hess
  have hgoal : A⁻¹ ≤ essInf (fun x => ENNReal.ofReal (u x)) μ := by
    apply (ENNReal.inv_le_inv).mp
    simpa using hinv
  simpa [CoarseDeGiorgi.nonnegativeEssInf, μ] using hgoal

end CoarseDeGiorgi.Harnack.Iterations
