import CoarseDeGiorgi.LowerFractional.GateSeminorm
import CoarseDeGiorgi.LowerFractional.LocalAuxNorm

/-! Local fractional estimate `e.lower.fractional.local` (Proposition `p.lower.fractional`). -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- The real weight sum over `𝒯_k(U)` as an extended-real sum. -/
lemma lower_local_weight_ofReal {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (q : ℝ) (U : Set (Vec d)) :
    ENNReal.ofReal (∑ η ∈ triangulationIn (d := d) k U,
        (volume (simplexCell k η)).toReal * ‖lowerResponseInvOnCell k a ha η‖ ^ q) =
      ∑ η ∈ triangulationIn (d := d) k U, volume (simplexCell k η) *
        ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun η _ =>
    mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal
    (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne]
  rfl

theorem lower_fractional_local_core_of_reconstruction
    (hreconstruction : LowerReconstructionHypothesis)
    {d : ℕ} [NeZero d] {q t : ℝ} (hq : 1 < q) (ht : 0 < t) (ht1 : t < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : CoeffField d)
      (ha : IsWeightedCoeffOn (Aliases.originCube 1) a) (n : ℕ) (z : Fin d → ℤ),
      auxCube ((n : ℤ) + 1) z ⊆ Aliases.originCube 1 →
      ∀ (w : Vec d → ℝ) (G : Vec d → Vec d),
        MemH1a a (auxCube ((n : ℤ) + 1) z) w G →
        MemLp w (ENNReal.ofReal (paramR q)) (volume.restrict (auxCube ((n : ℤ) + 1) z)) →
          fracSeminorm (auxCube ((n : ℤ) + 1) z) (alphaParam t) (paramR q) w ≤
            ENNReal.ofReal C * (weightedEnergy a (auxCube ((n : ℤ) + 1) z) G) ^ (1 / 2 : ℝ) *
              ∑' k : ℕ, if n < k then
                ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
                  (∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
                    volume (simplexCell k η) *
                      ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)) ^
                    (1 / (2 * q)) else 0 := by
  obtain ⟨C, hC, hrec⟩ := weighted_fractional_reconstruction_of_reconstruction
    hreconstruction (d := d) (α := alphaParam t) (r := paramR q)
    (by unfold alphaParam; linarith) (by unfold alphaParam; linarith)
    (lower_paramR_gt_one hq)
  refine ⟨C, hC, ?_⟩
  intro a ha n z hQ w G hw hwLp
  have haQ := weightedCoeffOn_mono ha hQ
  have hb := hrec ((n : ℤ) + 1) z a haQ w G hw hwLp
  refine hb.trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  calc
    _ ≤ ∑' k : {k : ℤ // (n : ℤ) + 1 ≤ k},
        (ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * t)) *
          (ENNReal.ofReal (∑ η ∈ triangulationIn (d := d) k.1.toNat (auxCube ((n : ℤ) + 1) z),
            (volume (simplexCell k.1.toNat η)).toReal *
              ‖lowerResponseInvOnCell k.1.toNat a ha η‖ ^ q)) ^ (1 / (2 * q))) *
            (weightedEnergy a (auxCube ((n : ℤ) + 1) z) G) ^ (1 / 2 : ℝ) := by
      apply ENNReal.tsum_le_tsum
      intro k
      rw [show 1 - alphaParam t = t by unfold alphaParam; ring, mul_assoc]
      exact mul_le_mul' le_rfl (lower_auxAverage_norm_local _ k.1 k.2 z a ha hQ haQ hw hq)
    _ = (∑' k : {k : ℤ // (n : ℤ) + 1 ≤ k},
        ENNReal.ofReal ((3 : ℝ) ^ (-(k.1 : ℝ) * t)) *
          (ENNReal.ofReal (∑ η ∈ triangulationIn (d := d) k.1.toNat (auxCube ((n : ℤ) + 1) z),
            (volume (simplexCell k.1.toNat η)).toReal *
              ‖lowerResponseInvOnCell k.1.toNat a ha η‖ ^ q)) ^ (1 / (2 * q))) *
            (weightedEnergy a (auxCube ((n : ℤ) + 1) z) G) ^ (1 / 2 : ℝ) :=
      ENNReal.tsum_mul_right
    _ ≤ _ := by
      rw [mul_comm]
      refine mul_le_mul' le_rfl ?_
      let i : {k : ℤ // (n : ℤ) + 1 ≤ k} → ℕ := fun k => k.1.toNat
      have hnn : ∀ k : {k : ℤ // (n : ℤ) + 1 ≤ k}, 0 ≤ k.1 := fun k => by
        have := k.2; omega
      have hi : Function.Injective i := by
        intro k l h
        apply Subtype.ext
        simpa only [i, Int.toNat_of_nonneg (hnn k), Int.toNat_of_nonneg (hnn l)] using
          congrArg (fun n : ℕ => (n : ℤ)) h
      convert ENNReal.tsum_comp_le_tsum_of_injective hi (fun k : ℕ =>
        if n < k then ENNReal.ofReal (Real.rpow 3 (-((k : ℝ) * t))) *
          (∑ η ∈ triangulationIn (d := d) k (auxCube ((n : ℤ) + 1) z),
            volume (simplexCell k η) *
              ENNReal.ofReal (Real.rpow ‖lowerResponseInvOnCell k a ha η‖ q)) ^
            (1 / (2 * q)) else 0) using 1
      refine tsum_congr fun k => ?_
      have hk : ((k.1.toNat : ℕ) : ℝ) = (k.1 : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (hnn k)
      have hlt : n < k.1.toNat := by have := k.2; omega
      simp only [i, hlt, ↓reduceIte]
      rw [lower_local_weight_ofReal, hk, neg_mul]
      rfl
