import CoarseDeGiorgi.Localization.SourceCover
import CoarseDeGiorgi.Localization.LowerFractional

namespace CoarseDeGiorgi.Assembly

open Homogenization MeasureTheory Set CoarseDeGiorgi.Localization
open scoped BigOperators ENNReal

/-- Localization with the measurable density representative used by the lift contract.
Only its agreement on the outer cube is needed. -/
theorem hybrid_localization_rpow_of_density {d : ℕ} [NeZero d] {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) (hr2 : r < 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ 0 < C ∧
      ∀ δ : ℝ, 0 < δ → ∀ m : ℤ, gridSpacing m ≤ 1 → δ / 192 < gridSpacing m →
      ∀ (K : Set (Vec d)) (a R : ℝ),
      (∀ y ∈ K, ∀ i, |y i| ≤ a / 2) → a + 4 * gridSpacing m < R →
      ∀ (L : ℝ≥0∞) (coeff : CoeffField d) (G : Vec d → Vec d) (w : Vec d → ℝ),
      Measurable w → ∀ g : Vec d → ℝ≥0∞, Measurable g →
      g =ᵐ[volume.restrict (radiusCube R)]
        (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (coeff x) (G x)))) →
      (∀ z ∈ coverIndices m K, fracNorm (auxCube m z) α r w < ⊤) →
      (∀ z ∈ coverIndices m K, fracSeminorm (auxCube m z) α r w ≤
        L * weightedEnergy coeff (auxCube m z) G ^ (1 / 2 : ℝ)) →
      fracNorm univ α r (localizedFunction m (coverIndices m K) w) ^ r ≤
        C * ((coverIndices m K).card : ℝ≥0∞) ^ (1 - r / 2) *
          ((4 ^ d : ℕ) : ℝ≥0∞) ^ (r / 2) *
          (L * weightedEnergy coeff (radiusCube R) G ^ (1 / 2 : ℝ)) ^ r +
        C * ENNReal.ofReal (δ ^ (-α * r)) * ((4 ^ d : ℕ) : ℝ≥0∞) *
          eLpNorm w (ENNReal.ofReal r) (volume.restrict (radiusCube R)) ^ r := by
  obtain ⟨C, hCfin, hCpos, hsum⟩ := exists_localization_sum_gap_constant (d := d) hα0 hα1 hr
  refine ⟨C, hCfin, hCpos, ?_⟩
  intro δ hδ m hs hgap K a R hK hm L coeff G w hw g hg hdensity hfin hlocal
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hS : (∑ z ∈ coverIndices m K, fracSeminorm (auxCube m z) α r w ^ r) ≤
      ((coverIndices m K).card : ℝ≥0∞) ^ (1 - r / 2) *
        ((4 ^ d : ℕ) : ℝ≥0∞) ^ (r / 2) *
        (L * weightedEnergy coeff (radiusCube R) G ^ (1 / 2 : ℝ)) ^ r := by
    have hp : (∑ z ∈ coverIndices m K, fracSeminorm (auxCube m z) α r w ^ r) ≤
        L ^ r * ∑ z ∈ coverIndices m K, weightedEnergy coeff (auxCube m z) G ^ (r / 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have h := ENNReal.rpow_le_rpow (hlocal z hz) hr0.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * r = r / 2 by ring] at h
      exact h
    have heq : (∫⁻ x in radiusCube R, g x) = weightedEnergy coeff (radiusCube R) G :=
      lintegral_congr_ae hdensity
    have heqQ (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) :
        (∫⁻ x in auxCube m z, g x) = weightedEnergy coeff (auxCube m z) G :=
      lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset
        ((auxCube_subset_closedAuxCube m z).trans (selected_closedAuxCube_subset hK hm hz)) hdensity)
    have hglobal := sum_local_energy_rpow_le hK hm
      (show 0 < r / 2 by positivity) (show r / 2 < 1 by linarith only [hr2]) hg
    rw [heq] at hglobal
    have heqSum : (∑ z ∈ coverIndices m K, (∫⁻ x in auxCube m z, g x) ^ (r / 2)) =
        ∑ z ∈ coverIndices m K, weightedEnergy coeff (auxCube m z) G ^ (r / 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [heqQ z hz]
    rw [heqSum] at hglobal
    change (∑ z ∈ coverIndices m K, weightedEnergy coeff (auxCube m z) G ^ (r / 2)) ≤
      ((coverIndices m K).card : ℝ≥0∞) ^ (1 - r / 2) *
        ((4 ^ d : ℕ) : ℝ≥0∞) ^ (r / 2) * weightedEnergy coeff (radiusCube R) G ^ (r / 2) at hglobal
    apply hp.trans
    have h := mul_le_mul_right hglobal (L ^ r)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * r = r / 2 by ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hM := sum_local_eLpNorm_rpow_le hr0 hK hm hw
  apply (hsum δ hδ m hs hgap (coverIndices m K) w hw hfin).trans
  apply add_le_add
  · simpa only [mul_assoc] using mul_le_mul_right hS C
  · simpa only [mul_assoc] using
      mul_le_mul_right hM (C * ENNReal.ofReal (δ ^ (-α * r)))

end CoarseDeGiorgi.Assembly
