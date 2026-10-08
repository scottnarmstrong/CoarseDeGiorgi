import CoarseDeGiorgi.Endpoint.Reconstruction.FineCells
import CoarseDeGiorgi.LowerFractional.AuxNorm
import CoarseDeGiorgi.Weighted.ZeroBoundary

/-! # The fine projection's same-index spatial norm bound

The step field uses cubes of side `3^(-k)`. Its norm is bounded by the response
moment at index `k`, rather than by the moment at index `k+1`.
-/

namespace CoarseDeGiorgi.Endpoint.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def fineAverage {d : ℕ} (k : ℕ) (G : Vec d → Vec d) : Vec d → Vec d := by
  classical
  exact ∑ j : Fin d → Fin (3 ^ k),
    (fineCube k j).indicator (fun _ => volumeAverageVec (fineCube k j) G)

theorem measurableSet_fineCube {d : ℕ} (k : ℕ) (j : Fin d → Fin (3 ^ k)) :
    MeasurableSet (fineCube k j) := by
  unfold fineCube Foundations.Simplex.simplexCube
  have heq : {x : Vec d | ∀ i, -(3 : ℝ) ^ (-(k : ℤ)) / 2 <
      x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) ∧
      x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) <
        (3 : ℝ) ^ (-(k : ℤ)) / 2} =
      ⋂ i : Fin d, {x : Vec d | -(3 : ℝ) ^ (-(k : ℤ)) / 2 <
        x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) ∧
        x i - (3 : ℝ) ^ (-(k : ℤ)) * (gridOffset k j i : ℝ) <
          (3 : ℝ) ^ (-(k : ℤ)) / 2} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (isOpen_lt continuous_const ((continuous_apply i).sub continuous_const)).measurableSet.inter
      (isOpen_lt ((continuous_apply i).sub continuous_const) continuous_const).measurableSet

theorem measurable_fineAverage {d : ℕ} (k : ℕ) (G : Vec d → Vec d) :
    Measurable (fineAverage k G) := by
  classical
  change Measurable (fun x => fineAverage k G x)
  simp only [fineAverage, Finset.sum_apply]
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator (measurableSet_fineCube k j)

/-- A finite step field belongs to every Lebesgue space, including `L∞`. -/
theorem memLp_fineAverage {d : ℕ} (k : ℕ) (G : Vec d → Vec d) (p : ℝ≥0∞) :
    MemLp (fineAverage k G) p volume := by
  classical
  have hsum : MemLp (fun x => ∑ j : Fin d → Fin (3 ^ k),
      (fineCube k j).indicator (fun _ => volumeAverageVec (fineCube k j) G) x) p volume := by
    apply memLp_finsetSum
    intro j _
    apply memLp_indicator_const p (measurableSet_fineCube k j)
    right
    rw [fineCube, Foundations.Simplex.volume_simplexCube]
    exact ENNReal.ofReal_ne_top
  have heq : fineAverage k G = fun x => ∑ j : Fin d → Fin (3 ^ k),
      (fineCube k j).indicator (fun _ => volumeAverageVec (fineCube k j) G) x := by
    funext x
    simp only [fineAverage, Finset.sum_apply]
  rw [heq]
  exact hsum

theorem fine_average_rpow_pointwise {d : ℕ} (k : ℕ) (G : Vec d → Vec d)
    {r : ℝ} (hr : 0 < r) (x : Vec d) :
    (ENNReal.ofReal (euclidNorm (fineAverage k G x))) ^ r =
      ∑ j : Fin d → Fin (3 ^ k), (fineCube k j).indicator
        (fun _ => (ENNReal.ofReal (euclidNorm (volumeAverageVec (fineCube k j) G))) ^ r) x := by
  classical
  by_cases hx : ∃ j : Fin d → Fin (3 ^ k), x ∈ fineCube k j
  · obtain ⟨j, hxj⟩ := hx
    have hother : ∀ l : Fin d → Fin (3 ^ k), l ≠ j → x ∉ fineCube k l := by
      intro l hlj hxl
      exact Set.disjoint_left.mp (fine_cubes_pairwiseDisjoint k hlj.symm) hxj hxl
    have heq : fineAverage k G x = volumeAverageVec (fineCube k j) G := by
      simp only [fineAverage, Finset.sum_apply]
      rw [Finset.sum_eq_single j]
      · exact Set.indicator_of_mem hxj _
      · intro l _ hlj
        exact Set.indicator_of_notMem (hother l hlj) _
      · intro hj
        exact (hj (Finset.mem_univ _)).elim
    rw [heq, Finset.sum_eq_single j]
    · rw [Set.indicator_of_mem hxj]
    · intro l _ hlj
      exact Set.indicator_of_notMem (hother l hlj) _
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  · have hn : ∀ j : Fin d → Fin (3 ^ k), x ∉ fineCube k j :=
      fun j hj => hx ⟨j, hj⟩
    have heq : fineAverage k G x = 0 := by
      simp only [fineAverage, Finset.sum_apply]
      exact Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (hn j) _
    rw [heq]
    have hzero : euclidNorm (0 : Vec d) = 0 := by
      simp only [euclidNorm, vecNormSq, vecDot, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, Real.sqrt_zero]
    simp only [hzero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hr]
    exact (Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (hn j) _).symm

theorem fine_average_power_integral {d : ℕ} (k : ℕ) (G : Vec d → Vec d)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x, (ENNReal.ofReal (euclidNorm (fineAverage k G x))) ^ r ∂volume) =
      ENNReal.ofReal (∑ j : Fin d → Fin (3 ^ k), (volume (fineCube k j)).toReal *
        euclidNorm (volumeAverageVec (fineCube k j) G) ^ r) := by
  classical
  have hn (z : Vec d) : 0 ≤ euclidNorm z := Real.sqrt_nonneg _
  simp_rw [fine_average_rpow_pointwise k G hr]
  rw [lintegral_finsetSum]
  · rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (hn _) _))]
    apply Finset.sum_congr rfl
    intro j _
    have hvtop : volume (fineCube k j) ≠ ⊤ := by
      rw [fineCube, Foundations.Simplex.volume_simplexCube]
      exact ENNReal.ofReal_ne_top
    rw [lintegral_indicator (measurableSet_fineCube k j), lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvtop,
      ENNReal.ofReal_rpow_of_nonneg (hn _) hr.le, mul_comm]
  · intro j _
    exact measurable_const.indicator (measurableSet_fineCube k j)

theorem fine_average_norm_le {d : ℕ} [NeZero d] (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a a (CoarseDeGiorgi.originCube 1) v G) {q : ℝ} (hq : 1 < q) :
    eLpNorm (fun x => euclidNorm (fineAverage k G x)) (ENNReal.ofReal (paramR q))
        (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
      (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)) *
        (weightedEnergy a (CoarseDeGiorgi.originCube 1) G).rpow (1 / 2) := by
  have hr : 0 < paramR q := zero_lt_one.trans (LowerFractional.lower_paramR_gt_one hq)
  have hL := LowerFractional.lower_cellAverage_nonneg k a ha q
  have hE := (Weighted.MemH1a.energy_lt_top LowerFractional.lower_unitCube_domain.isOpen ha hv).ne
  have hi := ENNReal.ofReal_le_ofReal (fine_grid_spatial_holder k a ha hv hq)
  rw [← fine_average_power_integral k G hr,
    ENNReal.ofReal_mul (Real.rpow_nonneg hL _),
    ← ENNReal.ofReal_rpow_of_nonneg hL (by positivity),
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal hE] at hi
  have hm : AEStronglyMeasurable (fun x => euclidNorm (fineAverage k G x)) volume :=
    (Foundations.Euclid.continuous_eNorm2.measurable.comp
      (measurable_fineAverage k G)).aestronglyMeasurable
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top hm, ENNReal.toReal_ofReal hr.le]
  have he : (fun x => ‖euclidNorm (fineAverage k G x)‖ₑ ^ paramR q) =
      fun x => (ENNReal.ofReal (euclidNorm (fineAverage k G x))) ^ paramR q := by
    funext x
    rw [← ofReal_norm, Real.norm_of_nonneg
      (show 0 ≤ euclidNorm (fineAverage k G x) from Real.sqrt_nonneg _)]
  rw [he]
  have hh := ENNReal.rpow_le_rpow hi (div_nonneg zero_le_one hr.le)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hh
  have hexp : (paramR q / (2 * q)) * (1 / paramR q) = 1 / (2 * q) := by field_simp
  have hexp' : (paramR q / 2) * (1 / paramR q) = (1 / 2 : ℝ) := by field_simp
  rw [hexp, hexp'] at hh
  exact hh

/-- The fine-average bound applies directly to the weighted zero-boundary completion. -/
theorem fine_average_norm_le_zeroTrace {d : ℕ} [NeZero d] (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (CoarseDeGiorgi.originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a0 a (CoarseDeGiorgi.originCube 1) v G) {q : ℝ} (hq : 1 < q) :
    eLpNorm (fun x => euclidNorm (fineAverage k G x)) (ENNReal.ofReal (paramR q))
        (volume.restrict (CoarseDeGiorgi.originCube 1)) ≤
      (ENNReal.ofReal (lowerCellAverage a ha k q)).rpow (1 / (2 * q)) *
        (weightedEnergy a (CoarseDeGiorgi.originCube 1) G).rpow (1 / 2) :=
  fine_average_norm_le k a ha (Weighted.MemH1a0.memH1a ha hv) hq

end

end CoarseDeGiorgi.Endpoint.Reconstruction
