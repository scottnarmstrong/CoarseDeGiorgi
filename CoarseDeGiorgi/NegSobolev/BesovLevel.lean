import CoarseDeGiorgi.NegSobolev.BesovPartitionBounds
import CoarseDeGiorgi.NegSobolev.BesovPartitionLower

/-! # A complete level comparison for a finite equal-volume partition -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- Assemble the two `Lᵖ` estimates and express the step-function norm as the
arithmetic mean over the cells. -/
theorem besov_level_comparison {d : ℕ} {ι : Type*} [Fintype ι]
    (t : ℝ) (ht : 0 < t) (V : Set (Vec d)) (hV : MeasurableSet V)
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hsub : ∀ i, U i ⊆ V) (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hpart : volume.restrict V = ∑ i, volume.restrict (U i))
    (N : ℝ) (hN : 0 < N) (hvol : ∀ i, (volume (U i)).toReal = N⁻¹)
    (hfin : ∀ i, volume (U i) ≠ ⊤)
    (hdiam : ∀ i, ∀ x ∈ U i, ∀ y ∈ U i, vecNormSq (x - y) ≤ (d : ℝ) * t)
    (δ : ℝ) (hδ : 0 < δ)
    (hδvol : ∀ i, δ ≤ ((4 * Real.pi * t) ^ (-((d : ℝ) / 2)) *
      Real.exp (-((d : ℝ) / 4))) * (volume (U i)).toReal)
    (C : ℝ) (hC : 0 < C) (hCδ : δ⁻¹ ≤ C)
    (hCD : (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) ≤ C)
    (p : ℝ) (hp : 1 ≤ p) (b : Vec d → Mat d)
    (hb : ∀ r s, Integrable (fun y => b y r s) (volume.restrict V))
    (hpos : ∀ᵐ y ∂(volume.restrict V), (b y).PosSemidef) :
    let M := (ENNReal.ofReal ((∑ i, Real.rpow ‖volumeAverageMat (U i) b‖ p) / N)) ^ (1 / p)
    let H := eLpNorm (fun x => ‖Matrix.of fun r s =>
      ∫ y in V, gaussianKernel t ht (x - y) * b y r s‖) (ENNReal.ofReal p) volume
    ENNReal.ofReal C⁻¹ * M ≤ H ∧ H ≤ ENNReal.ofReal C * M := by
  classical
  dsimp only
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hvolpos (i : ι) : 0 < (volume (U i)).toReal := by rw [hvol i]; exact inv_pos.mpr hN
  have hlo := gaussianKernel_partition_eLpNorm_lower t ht V hV U hU hsub hvolpos hdisj
    b hb hpos hdiam δ hδ hδvol (ENNReal.ofReal p)
  have hup := gaussianKernel_partition_eLpNorm_upper t ht V hV U hU hvolpos hfin hpart b
    (fun i r s => IntegrableOn.mono_set (hb r s) (hsub i))
    (fun i => ae_restrict_of_ae_restrict_of_subset (hsub i) hpos) hdiam p hp
  rw [eLpNorm_partition_step_equal_volume U hU hdisj N hN hvol hfin
    (fun i => ‖volumeAverageMat (U i) b‖) (fun i => norm_nonneg _) p hp0] at hlo hup
  constructor
  · have hloC := hlo.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hCδ) _)
    have h := mul_le_mul_right hloC (ENNReal.ofReal C⁻¹)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hC.le), inv_mul_cancel₀ hC.ne',
      ENNReal.ofReal_one, one_mul] at h
    exact h
  · exact hup.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hCD) _)

end CoarseDeGiorgi.NegSobolev
