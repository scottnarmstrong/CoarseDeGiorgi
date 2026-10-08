import CoarseDeGiorgi.LowerFractional.GateSeminorm
import CoarseDeGiorgi.LowerFractional.NormBounds

/-! Lower fractional estimates on cubes contained in the unit cube. -/

namespace CoarseDeGiorgi.LowerFractional
open Homogenization MeasureTheory Aliases
open scoped ENNReal

/-- The bound `e.lower.fractional` from an explicit reconstruction
input (`LowerReconstructionHypothesis`). The constant depends only on d, q, t. -/
theorem lower_fractional_bound_of_reconstruction
    (hreconstruction : LowerReconstructionHypothesis) :
    ∀ d : ℕ, 3 ≤ d → ∀ q t : ℝ, (hq : 1 < q) → (ht : 0 < t) →
      ∃ C : ℝ, 0 < C ∧
        ∀ p s : ℝ, (hp : 1 < p) → (hs : 0 < s) →
          ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) →
            spatialMomentRange a ha p q s t →
            ∀ (m : ℤ) (z : Fin d → ℤ) (w : Vec d → ℝ) (G : Vec d → Vec d),
              auxCube m z ⊆ Aliases.originCube 1 → MemH1a a (auxCube m z) w G →
              fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
                ENNReal.ofReal C *
                  ENNReal.rpow (lowerMoment a ha t q ht (le_of_lt hq)) (-1 / 2) *
                  ENNReal.rpow (weightedEnergy a (auxCube m z) G) (1 / 2) := by
  intro d hd q t hq ht
  let : NeZero d := ⟨by omega⟩
  by_cases ht1 : t < 1
  · obtain ⟨C, hC, hbound⟩ := lower_fractional_h1a_of_reconstruction hreconstruction
      (d := d) hq ht ht1
    refine ⟨C, hC, ?_⟩
    intro p s hp hs a ha hrange m z w G hQ hw
    exact hbound a ha m z hQ w G hw
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p s hp hs a ha hrange
    exact (ht1 (lower_range_t_lt_one hd hrange)).elim


theorem lower_fractional_embedding_of_reconstruction
    (hreconstruction : LowerReconstructionHypothesis)
    {d : ℕ} (hd : 3 ≤ d) (p q s t : ℝ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t) (m : ℤ) (z : Fin d → ℤ)
    (hQ : auxCube m z ⊆ Aliases.originCube 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ w : Vec d → ℝ, ∀ G : Vec d → Vec d,
      MemH1a a (auxCube m z) w G →
      fracNorm (auxCube m z) (alphaParam t) (paramR q) w ≤
        C * h1aWeightedNorm a (auxCube m z) w G := by
  let : NeZero d := ⟨by omega⟩
  have hRange := hrange
  obtain ⟨hp, hq, hs, ht, hp', hq', _, _, htheta, hUpper, hLower⟩ := hRange
  have ht1 := lower_range_t_lt_one hd hrange
  have hr := lower_paramR_gt_one hq'
  obtain ⟨C, hC, hbound⟩ := lower_fractional_bound_of_reconstruction hreconstruction d hd q t hq' ht
  obtain ⟨D, hD, hmean⟩ := fractional_mean_norm_auxCube (d := d) (α := alphaParam t)
    hr.le (by unfold alphaParam; linarith)
  let B := ENNReal.ofReal C * (lowerMoment a ha t q ht hq'.le) ^ (-1 / 2 : ℝ)
  let M := ENNReal.ofReal (D * (3 : ℝ) ^ (-(m : ℝ) * alphaParam t))
  let V := (volume (auxCube m z)) ^ (1 / paramR q)
  let A := M * B + V
  have hB : B < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lower_moment_inverse_half_lt_top a ha t q ht hq'.le hLower)
  have hV : V < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity)
    (Foundations.Reconstruction.volume_auxCube_ne_top m z)
  have hA : A < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB, hV⟩
  refine ⟨(A ^ paramR q + B ^ paramR q) ^ (1 / paramR q), ?_, ?_⟩
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (ENNReal.add_lt_top.mpr ⟨ENNReal.rpow_lt_top_of_nonneg (zero_le_one.trans hr.le) hA.ne,
        ENNReal.rpow_lt_top_of_nonneg (zero_le_one.trans hr.le) hB.ne⟩).ne
  · intro w G hw
    have hsemi : fracSeminorm (auxCube m z) (alphaParam t) (paramR q) w ≤
        B * h1aWeightedNorm a (auxCube m z) w G :=
      (hbound p s hp' hs a ha hrange m z w G hQ hw).trans
        (mul_le_mul' le_rfl (lower_weighted_energy_norm_le a (auxCube m z) w G))
    have hLp : eLpNorm w (ENNReal.ofReal (paramR q)) (volume.restrict (auxCube m z)) ≤
        A * h1aWeightedNorm a (auxCube m z) w G := by
      have hb := hmean m z w hw.1
      refine hb.trans ((add_le_add (mul_le_mul' le_rfl hsemi)
        (mul_le_mul' (lower_weighted_mean_norm_le a (auxCube m z) w G) le_rfl)).trans_eq ?_)
      dsimp only [A, M, V]
      rw [add_mul]
      ac_rfl
    exact lower_fracNorm_bound (zero_lt_one.trans hr) w A B
      (h1aWeightedNorm a (auxCube m z) w G) hLp hsemi


end CoarseDeGiorgi.LowerFractional
