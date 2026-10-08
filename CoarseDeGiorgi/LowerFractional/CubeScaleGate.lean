module

public import CoarseDeGiorgi.LowerFractional.GateSeminorm
public import CoarseDeGiorgi.LowerFractional.LocalFractional

/-! Lower fractional estimates on cubes contained in the unit cube. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional
open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

theorem lower_fractional_scale_bound_of_reconstruction
    (hreconstruction : LowerReconstructionHypothesis) :
    ∀ d : ℕ, 3 ≤ d → ∀ q t : ℝ, 1 < q → 0 < t →
      ∃ C : ℝ, 0 < C ∧
        ∀ p s : ℝ, 1 < p → 0 < s →
          ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a),
            spatialMomentRange a ha p q s t →
            ∀ (n : ℕ) (z : Fin d → ℤ) (w : Vec d → ℝ) (G : Vec d → Vec d),
              auxCube ((n : ℤ) + 1) z ⊆ Aliases.originCube 1 →
              MemH1a a (auxCube ((n : ℤ) + 1) z) w G →
              fracSeminorm (auxCube ((n : ℤ) + 1) z) (alphaParam t) (paramR q) w ≤
                ENNReal.ofReal C *
                  (weightedEnergy a (auxCube ((n : ℤ) + 1) z) G).rpow (1 / 2) *
                  ∑' k : ℕ,
                    if n < k then
                      ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
                        (∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
                          volume (simplexCell k η) *
                            ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)).rpow
                          (1 / (2 * q))
                    else 0 := by
  intro d hd q t hq ht
  let : NeZero d := ⟨by omega⟩
  by_cases ht1 : t < 1
  · obtain ⟨C, hC, hcore⟩ := lower_fractional_local_core_of_reconstruction hreconstruction
      (d := d) hq ht ht1
    refine ⟨C, hC, ?_⟩
    intro p s hp hs a ha hrange n z w G hQ hw
    simp only [ENNReal.rpow_eq_pow]
    rw [mul_right_comm]
    apply fractional_bound_of_bounded_estimate (a := a) (α := alphaParam t) (r := paramR q)
      (K := ENNReal.ofReal C * ∑' k : ℕ,
        if n < k then
          ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
            (∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
              volume (simplexCell k η) *
                ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)) ^
              (1 / (2 * q)) else 0)
      (auxCube_isOpenBoundedConvexDomain _ z) (auxCube_nonempty _ z)
      (weightedCoeffOn_mono ha hQ)
      (zero_lt_one.trans (lower_paramR_gt_one hq)) ?_ hw
    intro v F hv hvLp
    have := hcore a ha n z hQ v F hv hvLp
    rw [mul_right_comm]
    exact this
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p s hp hs a ha hrange
    exact (ht1 (lower_range_t_lt_one hd hrange)).elim


end CoarseDeGiorgi.LowerFractional
