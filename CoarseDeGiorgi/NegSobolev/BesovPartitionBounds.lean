import CoarseDeGiorgi.NegSobolev.BesovCellBounds
import CoarseDeGiorgi.NegSobolev.BesovPartitionLp

/-! # Summing the upper Gaussian comparisons over a finite partition -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.NegSobolev

/-- Gaussian averaging of a finite partition step function is the corresponding
sum of Gaussian cell masses. No disjointness is needed for this identity. -/
theorem gaussianKernel_integral_partition_step_eq {d : ℕ} {ι : Type*} [Fintype ι]
    (t : ℝ) (ht : 0 < t) (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (a : ι → ℝ) (x : Vec d) :
    (∫ y, gaussianKernel t ht (x - y) * ∑ i, (U i).indicator (fun _ => a i) y) =
      ∑ i, (∫ y in U i, gaussianKernel t ht (x - y)) * a i := by
  classical
  have hG : Integrable (fun y => gaussianKernel t ht (x - y)) volume :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (integrable_gaussianKernel t ht)
  have heq (i : ι) : (fun y => gaussianKernel t ht (x - y) * (U i).indicator (fun _ => a i) y) =
      (U i).indicator (fun y => gaussianKernel t ht (x - y) * a i) := by
    funext y
    by_cases hy : y ∈ U i
    · simp only [Set.indicator_of_mem hy]
    · simp only [Set.indicator_of_notMem hy, mul_zero]
  have hi (i : ι) : Integrable
      (fun y => gaussianKernel t ht (x - y) * (U i).indicator (fun _ => a i) y) volume := by
    rw [heq i]
    exact (hG.mul_const (a i)).indicator (hU i)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [heq i, integral_indicator (hU i), integral_mul_const]

/-- The upper pointwise matrix estimate after summing over a finite partition.
The partition is encoded as an equality of restricted measures. -/
theorem gaussianKernel_partition_upper {d : ℕ} {ι : Type*} [Fintype ι]
    (t : ℝ) (ht : 0 < t) (V : Set (Vec d)) (U : ι → Set (Vec d))
    (hU : ∀ i, MeasurableSet (U i)) (hvol : ∀ i, 0 < (volume (U i)).toReal)
    (hfin : ∀ i, volume (U i) ≠ ⊤)
    (hpart : volume.restrict V = ∑ i, volume.restrict (U i))
    (b : Vec d → Mat d)
    (hb : ∀ i r s, Integrable (fun y => b y r s) (volume.restrict (U i)))
    (hpos : ∀ i, ∀ᵐ y ∂(volume.restrict (U i)), (b y).PosSemidef)
    (hdiam : ∀ i, ∀ y ∈ U i, ∀ z ∈ U i, vecNormSq (y - z) ≤ (d : ℝ) * t)
    (x : Vec d) :
    ‖Matrix.of fun r s => ∫ y in V, gaussianKernel t ht (x - y) * b y r s‖ ≤
      ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)) *
        ∫ y, gaussianKernel (2 * t) (by positivity) (x - y) *
          ∑ i, (U i).indicator (fun _ => ‖volumeAverageMat (U i) b‖) y := by
  classical
  have hi (i : ι) (r s : Fin d) :
      Integrable (fun y => gaussianKernel t ht (x - y) * b y r s) (volume.restrict (U i)) := by
    refine (hb i r s).bdd_mul (c := (4 * Real.pi * t) ^ (-((d : ℝ) / 2)))
      (((continuous_gaussianKernel t ht).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable.restrict) ?_
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.norm_of_nonneg (gaussianKernel_nonneg t ht (x - y))]
    exact gaussianKernel_le_prefactor t ht (x - y)
  have hdecomp : (Matrix.of fun r s => ∫ y in V, gaussianKernel t ht (x - y) * b y r s) =
      ∑ i, (Matrix.of fun r s => ∫ y in U i, gaussianKernel t ht (x - y) * b y r s) := by
    ext r s
    simp only [Matrix.of_apply, Matrix.sum_apply]
    rw [hpart]
    exact integral_finsetSum_measure (fun i _ => hi i r s)
  rw [hdecomp, gaussianKernel_integral_partition_step_eq (2 * t) (by positivity) U hU
    (fun i => ‖volumeAverageMat (U i) b‖) x]
  calc
    _ ≤ ∑ i, ‖Matrix.of fun r s => ∫ y in U i, gaussianKernel t ht (x - y) * b y r s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)) *
        (∫ y in U i, gaussianKernel (2 * t) (by positivity) (x - y)) *
          ‖volumeAverageMat (U i) b‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact gaussianKernel_cell_upper t ht (U i) (hU i) (hvol i) (hfin i) b (hb i)
        (hpos i) x (hdiam i)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

/-- The upper `Lᵖ` estimate for an arbitrary finite positive-matrix partition,
obtained by applying Gaussian contraction to its scalar step function. -/
theorem gaussianKernel_partition_eLpNorm_upper {d : ℕ} {ι : Type*} [Fintype ι]
    (t : ℝ) (ht : 0 < t) (V : Set (Vec d)) (hV : MeasurableSet V)
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hvol : ∀ i, 0 < (volume (U i)).toReal) (hfin : ∀ i, volume (U i) ≠ ⊤)
    (hpart : volume.restrict V = ∑ i, volume.restrict (U i))
    (b : Vec d → Mat d)
    (hb : ∀ i r s, Integrable (fun y => b y r s) (volume.restrict (U i)))
    (hpos : ∀ i, ∀ᵐ y ∂(volume.restrict (U i)), (b y).PosSemidef)
    (hdiam : ∀ i, ∀ y ∈ U i, ∀ z ∈ U i, vecNormSq (y - z) ≤ (d : ℝ) * t)
    (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun x => ‖Matrix.of fun r s => ∫ y in V, gaussianKernel t ht (x - y) * b y r s‖)
        (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)) *
        eLpNorm (fun x => ∑ i, (U i).indicator (fun _ => ‖volumeAverageMat (U i) b‖) x)
          (ENNReal.ofReal p) volume := by
  classical
  let F : Vec d → ℝ := fun x => ∑ i, (U i).indicator (fun _ => ‖volumeAverageMat (U i) b‖) x
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hF : Measurable F := Finset.measurable_sum _
    (fun i _ => measurable_const.indicator (hU i))
  have hF0 (x : Vec d) : 0 ≤ F x := Finset.sum_nonneg
    (fun i _ => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x)
  have hbV (r s : Fin d) : Integrable (fun y => b y r s) (volume.restrict V) := by
    rw [hpart]
    exact integrable_finsetSum_measure.mpr (fun i _ => hb i r s)
  have hH := (aestronglyMeasurable_gaussianKernel_set_matrix t ht V hV b hbV).norm
  have hconv0 (x : Vec d) : 0 ≤ ∫ y, gaussianKernel (2 * t) (by positivity) (x - y) * F y :=
    integral_nonneg (fun y => mul_nonneg (gaussianKernel_nonneg _ _ _) (hF0 y))
  have hmono : eLpNorm (fun x => ‖Matrix.of fun r s =>
      ∫ y in V, gaussianKernel t ht (x - y) * b y r s‖) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => D * ∫ y, gaussianKernel (2 * t) (by positivity) (x - y) * F y)
        (ENNReal.ofReal p) volume := by
    apply eLpNorm_mono hH
    intro x
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (mul_nonneg hD (hconv0 x))]
    exact gaussianKernel_partition_upper t ht V U hU hvol hfin hpart b hb hpos hdiam x
  have hfactor : eLpNorm (fun x => D * ∫ y, gaussianKernel (2 * t) (by positivity) (x - y) * F y)
      (ENNReal.ofReal p) volume = ENNReal.ofReal D *
      eLpNorm (fun x => ∫ y, gaussianKernel (2 * t) (by positivity) (x - y) * F y)
        (ENNReal.ofReal p) volume := by
    change eLpNorm (D • (fun x => ∫ y, gaussianKernel (2 * t) (by positivity) (x - y) * F y))
      (ENNReal.ofReal p) volume = _
    rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg hD]
  rw [hfactor] at hmono
  apply hmono.trans
  apply mul_le_mul_right
  exact eLpNorm_gaussianKernel_integral_smul_le (2 * t) (by positivity) F
    hF.aestronglyMeasurable p hp

end CoarseDeGiorgi.NegSobolev
