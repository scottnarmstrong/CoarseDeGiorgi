import CoarseDeGiorgi.LowerFractional.SpatialWeights
import CoarseDeGiorgi.LowerFractional.MeanGradient
import CoarseDeGiorgi.LowerFractional.Holder
import CoarseDeGiorgi.Statements.EuclidNorm

/-! Hölder for the actual simplex response weights and restricted H1a pairs.
The incidence and disjointness inputs are geometric, not analytic estimates. -/

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- The source mean-gradient estimate with the cell volume cleared. -/
theorem simplex_mean_gradient {d : ℕ} [NeZero d] (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a)
    (η : SimplexIndex d k) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a (simplexCell k η) w G) :
    (volume (simplexCell k η)).toReal *
        euclidNorm (volumeAverageVec (simplexCell k η) G) ^ 2 ≤
      ‖lowerResponseInvOnCell k a ha η‖ * (weightedEnergy a (simplexCell k η) G).toReal := by
  have hV := simplexCell_isOpenBoundedConvexDomain k η
  have hc := weightedCoeffOn_simplexCell k a ha η
  have hv : 0 < (volume (simplexCell k η)).toReal :=
    ENNReal.toReal_pos ((hV.isOpen.measure_pos volume (simplexCell_nonempty k η)).ne')
      hV.isBoundedDomain.isBounded.measure_lt_top.ne
  have hb := lower_mean_gradient_norm hV (simplexCell_nonempty k η) hc hw
  have hAvg : volumeAverage (simplexCell k η)
      (fun x => vecDot (G x) (matVecMul (a x) (G x))) =
      (weightedEnergy a (simplexCell k η) G).toReal / (volume (simplexCell k η)).toReal := by
    rw [Weighted.energy_toReal hc hw.2.1]
    unfold volumeAverage
    ring
  rw [hAvg] at hb
  have he : euclidNorm (volumeAverageVec (simplexCell k η) G) ^ 2 =
      vecNormSq (volumeAverageVec (simplexCell k η) G) := Real.sq_sqrt (vecNormSq_nonneg _)
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hb hv.le
  change _ ≤ (volume (simplexCell k η)).toReal *
    (‖lowerResponseInvOnCell k a ha η‖ *
      ((weightedEnergy a (simplexCell k η) G).toReal / (volume (simplexCell k η)).toReal)) at hm
  convert hm using 1
  field_simp

/-- Hölder on a disjoint subcollection of the actual triangulation cells.
The coefficient is exactly lowerCellAverage, rather than an abstract weight. -/
theorem lower_simplex_spatial_holder {d : ℕ} [NeZero d] (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a)
    {Q : Set (Vec d)} (hQ : IsOpenBoundedConvexDomain Q) (hQne : Q.Nonempty)
    (haQ : IsWeightedCoeffOn Q a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a Q w G) (s : Finset (SimplexIndex d k))
    (hsub : ∀ η ∈ s, simplexCell k η ⊆ Q)
    (hdisj : Set.PairwiseDisjoint (s : Set (SimplexIndex d k)) (simplexCell k))
    {q : ℝ} (hq : 1 < q) :
    (∑ η ∈ s, (volume (simplexCell k η)).toReal *
      euclidNorm (volumeAverageVec (simplexCell k η) G) ^ (paramR q)) ≤
      (lowerCellAverage a ha k q) ^ (paramR q / (2 * q)) *
        (weightedEnergy a Q G).toReal ^ (paramR q / 2) := by
  classical
  let v : SimplexIndex d k → ℝ := fun η => (volume (simplexCell k η)).toReal
  let B : SimplexIndex d k → ℝ := fun η => ‖lowerResponseInvOnCell k a ha η‖
  let E : SimplexIndex d k → ℝ := fun η => (weightedEnergy a (simplexCell k η) G).toReal
  let M : SimplexIndex d k → ℝ := fun η => euclidNorm (volumeAverageVec (simplexCell k η) G)
  have hcell (η : SimplexIndex d k) (hη : η ∈ s) : MemH1a a (simplexCell k η) w G :=
    memH1a_restrict hQ hQne haQ (simplexCell_isOpenBoundedConvexDomain k η) (hsub η hη) hw
  have hv (η : SimplexIndex d k) (_hη : η ∈ s) : 0 < v η := by
    exact ENNReal.toReal_pos
      (((simplexCell_isOpenBoundedConvexDomain k η).isOpen.measure_pos volume
        (simplexCell_nonempty k η)).ne')
      (simplexCell_isOpenBoundedConvexDomain k η).isBoundedDomain.isBounded.measure_lt_top.ne
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hr : 0 < paramR q := by unfold paramR; positivity
  have hbalance : paramR q / (2 * q) + paramR q / 2 = 1 :=
    (spatial_holder_exponents hq).2.2
  have hh := lower_spatial_holder s v B E M hv (fun _ _ => norm_nonneg _)
    (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => Real.sqrt_nonneg _) hr hq0
    hbalance (fun η hη => simplex_mean_gradient k a ha η (hcell η hη))
  have hEsum : (∑ η ∈ s, E η) ≤ (weightedEnergy a Q G).toReal := by
    have hsum : (∑ η ∈ s, weightedEnergy a (simplexCell k η) G) ≤ weightedEnergy a Q G := by
      unfold weightedEnergy
      rw [← lintegral_biUnion_finset hdisj (fun η _ =>
        (simplexCell_isOpenBoundedConvexDomain k η).isOpen.measurableSet)]
      apply lintegral_mono_set
      exact Set.iUnion₂_subset fun η hη => hsub η hη
    have hEtop := Weighted.MemH1a.energy_lt_top hQ.isOpen haQ hw
    rw [show (∑ η ∈ s, E η) = (∑ η ∈ s, weightedEnergy a (simplexCell k η) G).toReal by
      exact (ENNReal.toReal_sum fun η hη =>
        (Weighted.MemH1a.energy_lt_top (simplexCell_isOpenBoundedConvexDomain k η).isOpen
          (weightedCoeffOn_simplexCell k a ha η) (hcell η hη)).ne).symm]
    exact ENNReal.toReal_mono hEtop.ne hsum
  exact hh.trans (mul_le_mul
    (Real.rpow_le_rpow (Finset.sum_nonneg fun η _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _))
      (lower_spatial_weight_subcollection_le k a ha q s) (by positivity))
    (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      hEsum (by positivity)) (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (le_trans (Finset.sum_nonneg fun η _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _))
      (lower_spatial_weight_subcollection_le k a ha q s)) _))


end CoarseDeGiorgi.LowerFractional
