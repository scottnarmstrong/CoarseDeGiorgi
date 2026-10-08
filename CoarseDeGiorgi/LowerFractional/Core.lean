module

public import CoarseDeGiorgi.LowerFractional.AuxNorm
public import CoarseDeGiorgi.LowerFractional.ReconstructionInput
public import CoarseDeGiorgi.LowerFractional.WeightedPassage

/-! Fractional core and weighted completion. The final wrappers discharge the
reconstruction interface with the theorem `fractional_reconstruction`. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal

/-- A transparent abbreviation matching the statement of `fractional_reconstruction`.
Intermediate lemmas use this interface; Final.lean discharges it with that theorem. -/
abbrev LowerReconstructionHypothesis : Prop :=
  ∀ {d : ℕ} {α r : ℝ}, 0 < α → α < 1 → 1 < r →
    ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (Dw : Vec d → Vec d),
        HasWeakGradientOn (auxCube m z) w Dw →
        IntegrableOn w (auxCube m z) volume →
        IntegrableOn Dw (auxCube m z) volume →
        MemLp w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) →
        fracSeminorm (auxCube m z) α r w ≤ ENNReal.ofReal C *
          ∑' k : {k : ℤ // m ≤ k},
            ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - α))) *
              eLpNorm (fun x => euclidNorm (auxAverage m k.1 z Dw x))
                (ENNReal.ofReal r) (volume.restrict (auxCube m z))

/-- (e.lower.fractional.core), with the reconstruction constant chosen before
the coefficient field, cube, and function. -/
theorem lower_fractional_core_of_reconstruction
    (hreconstruction : LowerReconstructionHypothesis)
    {d : ℕ} [NeZero d] {q t : ℝ} (hq : 1 < q) (ht : 0 < t) (ht1 : t < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffField d)
      (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (m : ℤ) (z : Fin d → ℤ),
      auxCube m z ⊆ Aliases.originCube 1 →
      ∀ (w : Vec d → ℝ) (G : Vec d → Vec d),
        MemH1a a (auxCube m z) w G →
        MemLp w (ENNReal.ofReal (paramR q)) (volume.restrict (auxCube m z)) →
          fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
            ENNReal.ofReal C * (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
              (weightedEnergy a (auxCube m z) G) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hrec⟩ := weighted_fractional_reconstruction_of_reconstruction
    hreconstruction (d := d) (α := alphaParam t) (r := paramR q)
    (by unfold alphaParam; linarith) (by unfold alphaParam; linarith)
    (lower_paramR_gt_one hq)
  let N := (1 - Real.rpow 3 (-t))⁻¹
  have hN : 0 < N := inv_pos.mpr (lower_series_normalization_pos ht)
  refine ⟨C * N, mul_pos hC hN, ?_⟩
  intro a ha m z hQ w G hw hwLp
  have haQ : IsWeightedCoeffOn (auxCube m z) a := weightedCoeffOn_mono ha hQ
  have hb := hrec m z a haQ w G hw hwLp
  have hm : 0 ≤ m := lower_aux_scale_nonneg m z hQ
  have hseries : (∑' k : {k : ℤ // m ≤ k},
      ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * (1 - alphaParam t))) *
        eLpNorm (fun x => euclidNorm (auxAverage m k.1 z G x))
          (ENNReal.ofReal (paramR q)) (volume.restrict (auxCube m z))) ≤
      (ENNReal.ofReal N * (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ)) *
        (weightedEnergy a (auxCube m z) G) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ∑' k : {k : ℤ // m ≤ k},
          (ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * t)) *
            (ENNReal.ofReal (lowerCellAverage a ha k.1.toNat q)) ^ (1 / (2 * q))) *
              (weightedEnergy a (auxCube m z) G) ^ (1 / 2 : ℝ) := by
        apply ENNReal.tsum_le_tsum
        intro k
        rw [show 1 - alphaParam t = t by unfold alphaParam; ring, mul_assoc]
        exact mul_le_mul' le_rfl (lower_auxAverage_norm m k.1 k.2 z a ha hQ haQ hw hq)
      _ = (∑' k : {k : ℤ // m ≤ k},
          ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * t)) *
            (ENNReal.ofReal (lowerCellAverage a ha k.1.toNat q)) ^ (1 / (2 * q))) *
              (weightedEnergy a (auxCube m z) G) ^ (1 / 2 : ℝ) := ENNReal.tsum_mul_right
      _ ≤ _ := mul_le_mul' (lower_moment_tail_series a ha t q ht hq.le m hm) le_rfl
  refine hb.trans ((mul_le_mul' le_rfl hseries).trans_eq ?_)
  rw [ENNReal.ofReal_mul hC.le]
  simp only [mul_assoc]

/-- The bounded-member estimate passes to every represented H1a pair by
weighted truncation and Fatou, without an Lr premise. -/
theorem lower_fractional_h1a_of_reconstruction
    (hreconstruction : LowerReconstructionHypothesis)
    {d : ℕ} [NeZero d] {q t : ℝ} (hq : 1 < q) (ht : 0 < t) (ht1 : t < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffField d)
      (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (m : ℤ) (z : Fin d → ℤ),
      auxCube m z ⊆ Aliases.originCube 1 →
      ∀ (w : Vec d → ℝ) (G : Vec d → Vec d),
        MemH1a a (auxCube m z) w G →
          fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
            ENNReal.ofReal C * (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
              (weightedEnergy a (auxCube m z) G) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hcore⟩ := lower_fractional_core_of_reconstruction hreconstruction
    (d := d) hq ht ht1
  refine ⟨C, hC, ?_⟩
  intro a ha m z hQ w G hw
  apply fractional_bound_of_bounded_estimate
    (auxCube_isOpenBoundedConvexDomain m z) (auxCube_nonempty m z) (weightedCoeffOn_mono ha hQ)
    (zero_lt_one.trans (lower_paramR_gt_one hq)) ?_ hw
  intro v F hv hvLp
  exact hcore a ha m z hQ v F hv hvLp


end CoarseDeGiorgi.LowerFractional
