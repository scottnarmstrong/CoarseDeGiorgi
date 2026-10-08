import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyInputs
import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyTranslation

/-! # Finite Minkowski, subsequences, and Fatou close the reconstruction telescope -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology

noncomputable section
variable {d : ℕ}

/-- All factors in the final bound are fixed before choosing the root cube. -/
def assemblyConstantENN (d : ℕ) (α r C₁ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((∫ u : Vec d, FracGeometry.cutoffRadial α r 1 u) ^ (1 / r)) *
    ENNReal.ofReal C₁ * (1 - ENNReal.ofReal ((3 : ℝ) ^ (-α)))⁻¹ *
      (ENNReal.ofReal ((3 : ℝ) ^ (1 - α)) * ((2 : ℝ≥0∞) ^ d) ^ (1 / r))

theorem assemblyConstantENN_ne_top {α r C₁ : ℝ} (hα : 0 < α) (hr : 0 < r) :
    assemblyConstantENN d α r C₁ ≠ ∞ := by
  have hgeo := assembly_geometric_constant_ne_top hα
  have href : ((2 : ℝ≥0∞) ^ d) ^ (1 / r) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hr.le)
    finiteness
  unfold assemblyConstantENN
  finiteness

/-- Steps 10 and 11 for an actual root, using the supplied block estimates. -/
theorem assembly_reconstruction_le_of_block_bounds [NeZero d] {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r)
    (m : ℤ) (z : Fin d → ℤ) {w : Vec d → ℝ} (hw : Measurable w)
    (Dw : Vec d → Vec d) (C₁ : ℝ)
    (htrans : ∀ (j : ℕ) (u : Vec d),
      eLpNorm (fun x => assemblyBlock m z w j (x + u) - assemblyBlock m z w j x)
        (ENNReal.ofReal r) (volume.restrict (reflectionBox m)) ≤
          ENNReal.ofReal C₁ * ENNReal.ofReal (min 1 (euclidNorm u / auxSide (m + j))) *
            assemblyGradientTail m z Dw r j)
    (hsmooth : Tendsto (fun n : ℕ =>
      eLpNorm (fun x => smoothAverage m (auxSide (m + n)) z w x - reflectedScalar m z w x)
        (ENNReal.ofReal r) (volume.restrict (reflectionBox m))) atTop (𝓝 0)) :
    CoarseDeGiorgi.fracSeminorm (CoarseDeGiorgi.auxCube m z) α r w ≤
      assemblyConstantENN d α r C₁ * assemblySourceSeries m z Dw α r := by
  let R : ℝ≥0∞ := ENNReal.ofReal
    ((∫ u : Vec d, FracGeometry.cutoffRadial α r 1 u) ^ (1 / r))
  let T : ℝ≥0∞ := ∑' j : ℕ, ENNReal.ofReal (auxSide (m + j) ^ (-α)) *
    assemblyGradientTail m z Dw r j
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hblock (j : ℕ) :
      CoarseDeGiorgi.fracSeminorm (reflectionPositiveBox m) α r (assemblyBlock m z w j) ≤
        (R * ENNReal.ofReal C₁) *
          (ENNReal.ofReal (auxSide (m + j) ^ (-α)) * assemblyGradientTail m z Dw r j) := by
    have h := assembly_block_le hα0 hα1 hr0 (auxSide_pos _)
      (isOpen_reflectionPositiveBox m).measurableSet (assembly_reflectionBox_measurable m)
      (assembly_positiveBox_subset m) (assembly_block_measurable m z hw j)
      (ENNReal.ofReal C₁ * assemblyGradientTail m z Dw r j) (fun u => by
        have hu := htrans j u
        simpa only [euclidNorm_eq_eNorm2, mul_assoc, mul_left_comm] using hu)
    exact h.trans_eq (by dsimp only [R]; ac_rfl)
  have hsum (n : ℕ) :
      CoarseDeGiorgi.fracSeminorm (reflectionPositiveBox m) α r
        (fun x => ∑ j ∈ Finset.range (n + 1), assemblyBlock m z w j x) ≤
        (R * ENNReal.ofReal C₁) * T := by
    refine (assembly_seminorm_sum_le _ hr _ α _ (assembly_block_measurable m z hw)).trans ?_
    calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), (R * ENNReal.ofReal C₁) *
          (ENNReal.ofReal (auxSide (m + j) ^ (-α)) * assemblyGradientTail m z Dw r j) :=
        Finset.sum_le_sum fun j _ => hblock j
      _ = (R * ENNReal.ofReal C₁) * ∑ j ∈ Finset.range (n + 1),
          ENNReal.ofReal (auxSide (m + j) ^ (-α)) * assemblyGradientTail m z Dw r j :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_right (ENNReal.sum_le_tsum _) _
  obtain ⟨ns, _, hns⟩ := assembly_exists_subsequence_ae hr0 hsmooth
  have hnsU := ae_restrict_of_ae_restrict_of_subset (assembly_positiveBox_subset m) hns
  have hg : Measurable (fun x => reflectedScalar m z w x - assemblyMean m z w) := by
    apply Measurable.sub_const
    apply hw.comp
    exact measurable_const.add (measurable_pi_iff.mpr fun i => (continuous_apply i).abs.measurable)
  have hlim : ∀ᵐ x ∂volume.restrict (reflectionPositiveBox m),
      Tendsto (fun n => ∑ j ∈ Finset.range (ns n + 1), assemblyBlock m z w j x) atTop
        (𝓝 (reflectedScalar m z w x - assemblyMean m z w)) := by
    filter_upwards [hnsU] with x hx
    simp only [assembly_block_telescope]
    exact hx.sub_const _
  have hFatou := assembly_seminorm_le_of_ae_tendsto hr0
    (fun n => by
      have hmeas : ∀ j, Measurable (assemblyBlock m z w j) := assembly_block_measurable m z hw
      fun_prop) hg hlim (fun n => hsum (ns n))
  rw [assembly_seminorm_sub_const, assembly_reflected_seminorm] at hFatou
  refine hFatou.trans ?_
  have ht := assembly_weighted_tails_le m α (assemblyAverageSize m z Dw r)
  have habs : (∑' k : ℕ, ENNReal.ofReal (auxSide (m + k) ^ (1 - α)) *
      assemblyAverageSize m z Dw r k) =
      (ENNReal.ofReal ((3 : ℝ) ^ (1 - α)) * ((2 : ℝ≥0∞) ^ d) ^ (1 / r)) *
        assemblySourceSeries m z Dw α r := by
    simp_rw [assemblyAverageSize_eq m z Dw hr0]
    exact assembly_absolute_series m z Dw α r
  change T ≤ _ at ht
  rw [habs] at ht
  exact (mul_le_mul_right ht (R * ENNReal.ofReal C₁)).trans_eq (by
    dsimp only [assemblyConstantENN, R]
    ac_rfl)

end
end CoarseDeGiorgi.Foundations.Reconstruction
