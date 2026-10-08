import CoarseDeGiorgi.NegSobolev.BesovCellBounds
import CoarseDeGiorgi.NegSobolev.BesovPartitionLp

/-! # The lower Gaussian comparison for a finite partition -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- A uniform lower bound on prefactor times cell volume gives the lower `Lᵖ`
comparison. Zero extension supplies the positive whole-space field. -/
theorem gaussianKernel_partition_eLpNorm_lower {d : ℕ} {ι : Type*} [Fintype ι]
    (t : ℝ) (ht : 0 < t) (V : Set (Vec d)) (hV : MeasurableSet V)
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hsub : ∀ i, U i ⊆ V) (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (b : Vec d → Mat d)
    (hb : ∀ r s, Integrable (fun y => b y r s) (volume.restrict V))
    (hpos : ∀ᵐ y ∂(volume.restrict V), (b y).PosSemidef)
    (hdiam : ∀ i, ∀ x ∈ U i, ∀ y ∈ U i, vecNormSq (x - y) ≤ (d : ℝ) * t)
    (δ : ℝ) (hδ : 0 < δ)
    (hδvol : ∀ i, δ ≤ ((4 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
      Real.exp (-((d : ℝ) / 4))) * (volume (U i)).toReal) (p : ℝ≥0∞) :
    eLpNorm (fun x => ∑ i, (U i).indicator (fun _ => ‖volumeAverageMat (U i) b‖) x) p volume ≤
      ENNReal.ofReal δ⁻¹ * eLpNorm (fun x => ‖Matrix.of fun r s =>
        ∫ y in V, gaussianKernel t ht (x - y) * b y r s‖) p volume := by
  classical
  apply eLpNorm_partition_step_le U hU hdisj (fun i => ‖volumeAverageMat (U i) b‖)
    (fun i => norm_nonneg _) δ⁻¹ (inv_nonneg.mpr hδ.le) _ (fun x => norm_nonneg _) p
  intro i x hx
  have h := gaussianKernel_cell_lower t ht (U i) (hU i) (hvol i) (V.indicator b)
    (integrable_indicator_matrix_entry hV b hb) (indicator_matrix_posSemidef hV b hpos)
    x (fun y hy => hdiam i x hx y hy)
  rw [volumeAverageMat_indicator_of_subset (U i) V (hU i) (hsub i) b] at h
  simp_rw [gaussianKernel_indicator_entry_eq t ht V hV b] at h
  have h' := (mul_le_mul_of_nonneg_right (hδvol i) (norm_nonneg (volumeAverageMat (U i) b))).trans h
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hδ).mpr
  simpa only [mul_comm, mul_assoc] using h'

end CoarseDeGiorgi.NegSobolev
