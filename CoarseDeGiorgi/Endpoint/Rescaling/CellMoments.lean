import CoarseDeGiorgi.Endpoint.Rescaling.FiniteAggregation
import CoarseDeGiorgi.Endpoint.Rescaling.ResponseCovariance
import CoarseDeGiorgi.Endpoint.Rescaling.LatticeCells
import CoarseDeGiorgi.Statements.UpperSubadditivityCountable
import CoarseDeGiorgi.Statements.LowerAggregationCountable
import CoarseDeGiorgi.Statements.UpperCellAverage
import CoarseDeGiorgi.Statements.LowerCellAverage

/-! Refinement and shifted finite-average bounds for both response families. -/

open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Endpoint.Rescaling

open Foundations.Simplex

/-- The shared positive-matrix and partition properties of the two responses. -/
structure ResponseFamily (d : ℕ) where
  R : ∀ (a : CoeffField d) (U : Set (Vec d)), IsOpenBoundedConvexDomain U → U.Nonempty →
    IsWeightedCoeffOn U a → Mat d
  psd : ∀ a U hU hne ha, (R a U hU hne ha).PosSemidef
  agg : ∀ (a : CoeffField d) (U : Set (Vec d)) (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) (ha : IsWeightedCoeffOn U a) {ι : Type} [Countable ι]
    (V : ι → Set (Vec d)) (hV : ∀ i, IsOpenBoundedConvexDomain (V i))
    (hneV : ∀ i, (V i).Nonempty) (haV : ∀ i, IsWeightedCoeffOn (V i) a)
    (_hVU : ∀ i, V i ⊆ U) (_hdisj : Pairwise (Function.onFun Disjoint V))
    (_hcover : volume (U \ ⋃ i, V i) = 0),
    (∑' i, ((volume (V i)).toReal / (volume U).toReal) •
      R a (V i) (hV i) (hneV i) (haV i) - R a U hU hne ha).PosSemidef

noncomputable def upperFamily (d : ℕ) : ResponseFamily d where
  R := fun a U hU hne ha => upperResponse a U hU hne ha
  psd := fun _ _ hU hne ha => (upperResponse_spec hU hne ha).1.posSemidef
  agg := fun _a _U hU hne ha _ _ V hV hneV haV hVU hdisj hcover =>
    (upper_subadditivity_countable hU hne ha V hV hneV haV hVU hdisj hcover).2

noncomputable def lowerFamily (d : ℕ) : ResponseFamily d where
  R := fun a U hU hne ha => lowerResponseInv a U hU hne ha
  psd := fun _ _ hU hne ha => (lowerResponseInv_spec hU hne ha).1.posSemidef
  agg := fun _a _U hU hne ha _ _ V hV hneV haV hVU hdisj hcover =>
    (lower_aggregation_countable hU hne ha V hV hneV haV hVU hdisj hcover).2

noncomputable def cellResponse {d : ℕ} (D : ResponseFamily d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (η : SimplexIndex d k) : Mat d :=
  D.R a (simplexCell k η) (simplexCell_isOpenBoundedConvexDomain k η)
    (simplexCell_nonempty k η) (weightedCoeffOn_simplexCell k a ha η)

noncomputable def cellAverage {d : ℕ} (D : ResponseFamily d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (p : ℝ) : ℝ :=
  (∑ η : SimplexIndex d k, Real.rpow ‖cellResponse D a ha k η‖ p) /
    ((triangulation (d := d) k).card : ℝ)

theorem upperCellAverage_eq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (p : ℝ) :
    upperCellAverage a ha k p = cellAverage (upperFamily d) a ha k p := by
  classical
  unfold upperCellAverage cellAverage
  rw [← Finset.sum_coe_sort_eq_attach]
  rfl

theorem lowerCellAverage_eq {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (p : ℝ) :
    lowerCellAverage a ha k p = cellAverage (lowerFamily d) a ha k p := by
  classical
  unfold lowerCellAverage cellAverage
  rw [← Finset.sum_coe_sort_eq_attach]
  rfl

theorem parent_response_norm {d : ℕ} (D : ResponseFamily d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (π : Equiv.Perm (Fin d)) :
    ‖D.R a (kuhnSimplex 0 π 0) (isOpenBoundedConvexDomain_kuhnSimplex 0 π 0)
      (nonempty_kuhnSimplex 0 π 0)
      (LowerFractional.weightedCoeffOn_mono ha (unit_simplex_subset π))‖ ≤
      ((3 : ℝ) ^ d)⁻¹ * ∑ η : SimplexIndex d 1, ‖cellResponse D a ha 1 η‖ := by
  classical
  apply refined_norm_le π _ _ (D.psd _ _ _ _ _)
  exact D.agg a _ _ _ _ (fun η : RefinementIndex 1 π => simplexCell 1 η.1)
    (fun η => simplexCell_isOpenBoundedConvexDomain 1 η.1)
    (fun η => simplexCell_nonempty 1 η.1)
    (fun η => weightedCoeffOn_simplexCell 1 a ha η.1)
    (fun η => η.2) (refinement_pairwise_disjoint 1 π) (refinement_cover 1 π)

theorem simplexCell_zero {d : ℕ} (η : SimplexIndex d 0) :
    simplexCell 0 η = kuhnSimplex 0 η.1.2 0 := by
  obtain ⟨⟨j, π⟩, _, hj⟩ := Finset.mem_image.mp η.2
  have hz : η.1.1 = 0 := by
    rw [← hj]
    funext i
    have hj0 : (j i).val = 0 := by have := (j i).isLt; norm_num at this; omega
    simp only [gridOffset, Nat.pow_zero, Nat.sub_self, Nat.zero_div,
      Nat.cast_zero, sub_zero, Pi.zero_apply]
    exact_mod_cast hj0
  unfold simplexCell
  rw [Moments.simplex_eq_kuhnSimplex, hz]
  simp only [Nat.cast_zero, neg_zero, Pi.zero_apply, Int.cast_zero, mul_zero]
  rfl

/-- The exceptional scale-zero average is controlled by scale one with a dimension-only factor. -/
theorem cellAverage_zero_le {d : ℕ} (D : ResponseFamily d) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) {p : ℝ} (hp : 1 ≤ p) :
    cellAverage D a ha 0 p ≤ Real.rpow (Nat.factorial d : ℝ) p *
      cellAverage D a ha 1 p := by
  classical
  have hN : (0 : ℝ) < (triangulation (d := d) 1).card :=
    Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d 1)
  have : Nonempty (SimplexIndex d 1) := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (Assembly.ClassicalMomentsImpl.triangulation_card_pos d 1)
    exact ⟨⟨v, hv⟩⟩
  have hcard : Fintype.card (SimplexIndex d 1) = (triangulation (d := d) 1).card :=
    Fintype.card_coe _
  have hmean := finite_power_mean (fun η : SimplexIndex d 1 => ‖cellResponse D a ha 1 η‖)
    (fun _ => norm_nonneg _) hp
  rw [hcard] at hmean
  have hnorm (η : SimplexIndex d 0) :
      ‖cellResponse D a ha 0 η‖ ≤ (Nat.factorial d : ℝ) *
        ((∑ τ : SimplexIndex d 1, ‖cellResponse D a ha 1 τ‖) /
          (triangulation (d := d) 1).card) := by
    have h := parent_response_norm D a ha η.1.2
    have hc : cellResponse D a ha 0 η =
        D.R a (kuhnSimplex 0 η.1.2 0) (isOpenBoundedConvexDomain_kuhnSimplex _ _ _)
          (nonempty_kuhnSimplex _ _ _)
          (LowerFractional.weightedCoeffOn_mono ha (unit_simplex_subset _)) := by
      unfold cellResponse
      congr 1
      exact simplexCell_zero η
    rw [hc]
    convert h using 1
    rw [Moments.triangulation_card]
    simp only [Nat.one_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hf : (Nat.factorial d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
    field_simp
  have hpower (η : SimplexIndex d 0) : Real.rpow ‖cellResponse D a ha 0 η‖ p ≤
      Real.rpow (Nat.factorial d : ℝ) p * cellAverage D a ha 1 p := by
    calc
      _ ≤ Real.rpow ((Nat.factorial d : ℝ) *
          ((∑ τ : SimplexIndex d 1, ‖cellResponse D a ha 1 τ‖) /
            (triangulation (d := d) 1).card)) p :=
        Real.rpow_le_rpow (norm_nonneg _) (hnorm η) (by linarith only [hp])
      _ = Real.rpow (Nat.factorial d : ℝ) p *
          Real.rpow ((∑ τ : SimplexIndex d 1, ‖cellResponse D a ha 1 τ‖) /
            (triangulation (d := d) 1).card) p := Real.mul_rpow (by positivity) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hmean (Real.rpow_nonneg (by positivity) _)
  change ((∑ η : SimplexIndex d 0, Real.rpow ‖cellResponse D a ha 0 η‖ p) /
    (triangulation (d := d) 0).card) ≤ _
  apply (div_le_iff₀ (Nat.cast_pos.mpr
    (Assembly.ClassicalMomentsImpl.triangulation_card_pos d 0))).mpr
  calc
    _ ≤ ∑ _η : SimplexIndex d 0, Real.rpow (Nat.factorial d : ℝ) p *
        cellAverage D a ha 1 p := Finset.sum_le_sum (fun η _ => hpower η)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ]
      have hc0 : Fintype.card (SimplexIndex d 0) = (triangulation (d := d) 0).card :=
        Fintype.card_coe _
      rw [hc0, nsmul_eq_mul]
      ring

/-- A response-preserving cell injection bounds the restricted finite average. -/
theorem cellAverage_shift_le {d : ℕ} (D : ResponseFamily d)
    (a b : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hb : IsWeightedCoeffOn (originCube 1) b) (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (l : ℕ) (p : ℝ)
    (hcov : ∀ η : SimplexIndex d (l + 1), cellResponse D b hb (l + 1) η =
      cellResponse D a ha (l + 4) (latticeIndex z hz l η)) :
    cellAverage D b hb (l + 1) p ≤ (3 : ℝ) ^ (3 * d) *
      cellAverage D a ha (l + 4) p := by
  classical
  have hsum : (∑ η : SimplexIndex d (l + 1), Real.rpow ‖cellResponse D b hb (l + 1) η‖ p) ≤
      ∑ η : SimplexIndex d (l + 4), Real.rpow ‖cellResponse D a ha (l + 4) η‖ p := by
    simp_rw [hcov]
    exact sum_injective_le _ (latticeIndex_injective z hz l) _
      (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hN : (0 : ℝ) < (triangulation (d := d) (l + 1)).card :=
    Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d (l + 1))
  have hN' : (0 : ℝ) < (triangulation (d := d) (l + 4)).card :=
    Nat.cast_pos.mpr (Assembly.ClassicalMomentsImpl.triangulation_card_pos d (l + 4))
  have hratio : ((triangulation (d := d) (l + 4)).card : ℝ) =
      (3 : ℝ) ^ (3 * d) * (triangulation (d := d) (l + 1)).card := by
    rw [Moments.triangulation_card, Moments.triangulation_card]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [show (l + 4) * d = 3 * d + (l + 1) * d by ring, pow_add]
    ring
  unfold cellAverage
  calc
    _ ≤ (∑ η : SimplexIndex d (l + 4), Real.rpow ‖cellResponse D a ha (l + 4) η‖ p) /
        (triangulation (d := d) (l + 1)).card := div_le_div_of_nonneg_right hsum hN.le
    _ = _ := by rw [hratio]; field_simp

theorem upper_cellResponse_affine {d : ℕ} [NeZero d] (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hb : IsWeightedCoeffOn (originCube 1) (a ∘ affineMap (latticeCenter z) (1 / 27)))
    (l : ℕ) (η : SimplexIndex d (l + 1)) :
    cellResponse (upperFamily d) (a ∘ affineMap (latticeCenter z) (1 / 27)) hb (l + 1) η =
      cellResponse (upperFamily d) a ha (l + 4) (latticeIndex z hz l η) := by
  have he := affineImage_simplexCell z hz l η
  have hV : IsOpenBoundedConvexDomain
      (affineImage (latticeCenter z) (1 / 27) (simplexCell (l + 1) η)) :=
    he.symm ▸ simplexCell_isOpenBoundedConvexDomain _ _
  have hne : (affineImage (latticeCenter z) (1 / 27) (simplexCell (l + 1) η)).Nonempty :=
    he.symm ▸ simplexCell_nonempty _ _
  have haV : IsWeightedCoeffOn
      (affineImage (latticeCenter z) (1 / 27) (simplexCell (l + 1) η)) a :=
    he.symm ▸ weightedCoeffOn_simplexCell _ a ha _
  have h := upperResponse_affine (latticeCenter z) (by norm_num : (0 : ℝ) < 1 / 27)
    (simplexCell_isOpenBoundedConvexDomain _ _) (simplexCell_nonempty _ _) hV hne haV
  calc
    _ = upperResponse a _ hV hne haV := h
    _ = _ := by
      unfold cellResponse upperFamily
      congr 1

theorem lower_cellResponse_affine {d : ℕ} [NeZero d] (z : Fin d → ℤ)
    (hz : ∀ i, -39 ≤ z i ∧ z i ≤ 39) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    (hb : IsWeightedCoeffOn (originCube 1) (a ∘ affineMap (latticeCenter z) (1 / 27)))
    (l : ℕ) (η : SimplexIndex d (l + 1)) :
    cellResponse (lowerFamily d) (a ∘ affineMap (latticeCenter z) (1 / 27)) hb (l + 1) η =
      cellResponse (lowerFamily d) a ha (l + 4) (latticeIndex z hz l η) := by
  have he := affineImage_simplexCell z hz l η
  have hV : IsOpenBoundedConvexDomain
      (affineImage (latticeCenter z) (1 / 27) (simplexCell (l + 1) η)) :=
    he.symm ▸ simplexCell_isOpenBoundedConvexDomain _ _
  have hne : (affineImage (latticeCenter z) (1 / 27) (simplexCell (l + 1) η)).Nonempty :=
    he.symm ▸ simplexCell_nonempty _ _
  have haV : IsWeightedCoeffOn
      (affineImage (latticeCenter z) (1 / 27) (simplexCell (l + 1) η)) a :=
    he.symm ▸ weightedCoeffOn_simplexCell _ a ha _
  have h := lowerResponseInv_affine (latticeCenter z) (by norm_num : (0 : ℝ) < 1 / 27)
    (simplexCell_isOpenBoundedConvexDomain _ _) (simplexCell_nonempty _ _) hV hne haV
  calc
    _ = lowerResponseInv a _ hV hne haV := h
    _ = _ := by
      unfold cellResponse lowerFamily
      congr 1

end CoarseDeGiorgi.Endpoint.Rescaling
