module

public import CoarseDeGiorgi.Statements.UpperSubadditivityCountable
public import CoarseDeGiorgi.Statements.LowerAggregationCountable
public import CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import CoarseDeGiorgi.Statements.SimplexCellNonempty
public import CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell
public import CoarseDeGiorgi.Statements.CubeCellIsOpenBoundedConvexDomain
public import CoarseDeGiorgi.Statements.CubeCellNonempty
public import CoarseDeGiorgi.Statements.WeightedCoeffOnCubeCell
public import CoarseDeGiorgi.Statements.UpperResponseOnCube
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCube
public import CoarseDeGiorgi.Statements.UpperResponseOnCell
public import CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import CoarseDeGiorgi.Weighted.UpperSpecNorm

/-! # An abstract interface for the two response matrices

Both `upperResponse` and `lowerResponseInv` are positive semidefinite and satisfy the countable
subadditivity `R(U) ≤ ∑ |V_i|/|U| R(V_i)`; this is all the cubical comparison uses.
-/

@[expose] public section

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

structure RespData (d : ℕ) where
  R : ∀ (a : CoeffField d) (U : Set (Vec d)), IsOpenBoundedConvexDomain U → U.Nonempty →
    IsWeightedCoeffOn U a → Mat d
  psd : ∀ a U hU hU₀ ha, (R a U hU hU₀ ha).PosSemidef
  agg : ∀ (a : CoeffField d) (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U)
    (hU₀ : U.Nonempty) (ha : IsWeightedCoeffOn U a)
    {ι : Type} [Countable ι] (V : ι → Set (Vec d))
    (hV : ∀ i, IsOpenBoundedConvexDomain (V i)) (hV₀ : ∀ i, (V i).Nonempty)
    (haV : ∀ i, IsWeightedCoeffOn (V i) a)
    (_hVU : ∀ i, V i ⊆ U) (_hdisj : Pairwise (Function.onFun Disjoint V))
    (_hcover : volume (U \ ⋃ i, V i) = 0),
    Summable (fun i => ‖(((volume (V i)).toReal / (volume U).toReal : ℝ)) • R a (V i) (hV i) (hV₀ i) (haV i)‖) ∧
    (∑' i, (((volume (V i)).toReal / (volume U).toReal : ℝ)) • R a (V i) (hV i) (hV₀ i) (haV i) -
      R a U hU hU₀ ha).PosSemidef

noncomputable def upperData (d : ℕ) : RespData d where
  R := fun a U hU hU₀ ha => upperResponse a U hU hU₀ ha
  psd := fun _ _ hU hU₀ ha => (Weighted.UpperResponseImpl.upperResponse_posDef hU hU₀ ha).posSemidef
  agg := fun _ _ hU hU₀ ha _ _ V hV hV₀ haV hVU hdisj hcover =>
    CoarseDeGiorgi.upper_subadditivity_countable hU hU₀ ha V hV hV₀ haV hVU hdisj hcover

noncomputable def lowerData (d : ℕ) : RespData d where
  R := fun a U hU hU₀ ha => lowerResponseInv a U hU hU₀ ha
  psd := fun _ _ hU hU₀ ha => (Weighted.LowerResponseImpl.lowerResponseInv_posDef hU hU₀ ha).posSemidef
  agg := fun _ _ hU hU₀ ha _ _ V hV hV₀ haV hVU hdisj hcover =>
    CoarseDeGiorgi.lower_aggregation_countable hU hU₀ ha V hV hV₀ haV hVU hdisj hcover

/-- Norm domination from a positive semidefinite difference. -/
theorem norm_le_of_psd_sub {A B : Mat d} (hA : A.PosSemidef) (h : (B - A).PosSemidef) :
    ‖A‖ ≤ ‖B‖ := by
  apply Weighted.UpperResponseImpl.matrix_l2_norm_le_of_quadratic hA
  intro e
  have := qf_nonneg h e
  rw [qf_sub] at this
  exact sub_nonneg.mp this

namespace RespData

variable (D : RespData d)

/-- The response of a cube of `𝒬_j`. -/
noncomputable def cube (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) (j : ℕ)
    (z : Fin d → Fin (3 ^ j)) : Mat d :=
  D.R a (cubeCell j z) (cubeCell_isOpenBoundedConvexDomain j z) (cubeCell_nonempty j z)
    (weightedCoeffOn_cubeCell j a ha z)

/-- The response of a simplex of `𝒯_k`. -/
noncomputable def simplex (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ)
    (η : SimplexIndex d k) : Mat d :=
  D.R a (simplexCell k η) (simplexCell_isOpenBoundedConvexDomain k η) (simplexCell_nonempty k η)
    (weightedCoeffOn_simplexCell k a ha η)

/-- Subadditivity on norms. -/
theorem norm_le_tsum (a : CoeffField d) (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U)
    (hU₀ : U.Nonempty) (ha : IsWeightedCoeffOn U a)
    {ι : Type} [Countable ι] (V : ι → Set (Vec d))
    (hV : ∀ i, IsOpenBoundedConvexDomain (V i)) (hV₀ : ∀ i, (V i).Nonempty)
    (haV : ∀ i, IsWeightedCoeffOn (V i) a)
    (hVU : ∀ i, V i ⊆ U) (hdisj : Pairwise (Function.onFun Disjoint V))
    (hcover : volume (U \ ⋃ i, V i) = 0) :
    Summable (fun i => (volume (V i)).toReal / (volume U).toReal * ‖D.R a (V i) (hV i) (hV₀ i) (haV i)‖) ∧
    ‖D.R a U hU hU₀ ha‖ ≤ ∑' i, (volume (V i)).toReal / (volume U).toReal *
      ‖D.R a (V i) (hV i) (hV₀ i) (haV i)‖ := by
  obtain ⟨hs, hp⟩ := D.agg a U hU hU₀ ha V hV hV₀ haV hVU hdisj hcover
  have hvolU : 0 ≤ (volume U).toReal := ENNReal.toReal_nonneg
  have hnorm : ∀ i, ‖(((volume (V i)).toReal / (volume U).toReal : ℝ)) • D.R a (V i) (hV i) (hV₀ i) (haV i)‖ =
      (volume (V i)).toReal / (volume U).toReal * ‖D.R a (V i) (hV i) (hV₀ i) (haV i)‖ := by
    intro i
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg ENNReal.toReal_nonneg hvolU)]
  simp only [hnorm] at hs
  refine ⟨hs, ?_⟩
  have h1 := norm_le_of_psd_sub (D.psd a U hU hU₀ ha) hp
  have h2 : ‖∑' i, (((volume (V i)).toReal / (volume U).toReal : ℝ)) • D.R a (V i) (hV i) (hV₀ i) (haV i)‖ ≤
      ∑' i, ‖(((volume (V i)).toReal / (volume U).toReal : ℝ)) • D.R a (V i) (hV i) (hV₀ i) (haV i)‖ :=
    norm_tsum_le_tsum_norm (by simpa only [hnorm] using hs)
  simp only [hnorm] at h2
  exact h1.trans h2

end RespData

end CoarseDeGiorgi.Cubical
