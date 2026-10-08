module

public import CoarseDeGiorgi.LowerFractional.CellHolder

/-! Local Hölder: the weight is a sum over a given family of cells. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Aliases
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-- Local form of `lower_simplex_spatial_holder`: the weight is the sum over a
finite family `T` containing the disjoint subcollection `s`. -/
theorem lower_simplex_spatial_holder_local {d : ℕ} [NeZero d] (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (Aliases.originCube 1) a)
    {Q : Set (Vec d)} (hQ : IsOpenBoundedConvexDomain Q) (hQne : Q.Nonempty)
    (haQ : IsWeightedCoeffOn Q a) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a Q w G) (s : Finset (SimplexIndex d k))
    (T : Finset (SimplexIndex d k)) (hsT : s ⊆ T)
    (hsub : ∀ η ∈ s, simplexCell k η ⊆ Q)
    (hdisj : Set.PairwiseDisjoint (s : Set (SimplexIndex d k)) (simplexCell k))
    {q : ℝ} (hq : 1 < q) :
    (∑ η ∈ s, (volume (simplexCell k η)).toReal *
      euclidNorm (volumeAverageVec (simplexCell k η) G) ^ (paramR q)) ≤
      (∑ η ∈ T, (volume (simplexCell k η)).toReal *
        ‖lowerResponseInvOnCell k a ha η‖ ^ q) ^ (paramR q / (2 * q)) *
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
  have hTw : (∑ η ∈ s, (volume (simplexCell k η)).toReal *
      ‖lowerResponseInvOnCell k a ha η‖ ^ q) ≤ ∑ η ∈ T, (volume (simplexCell k η)).toReal *
      ‖lowerResponseInvOnCell k a ha η‖ ^ q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsT fun η _ _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
  exact hh.trans (mul_le_mul
    (Real.rpow_le_rpow (Finset.sum_nonneg fun η _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _))
      (hTw) (by positivity))
    (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
      hEsum (by positivity)) (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (le_trans (Finset.sum_nonneg fun η _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (norm_nonneg _) _))
      (hTw)) _))


end CoarseDeGiorgi.LowerFractional
