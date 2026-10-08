module

public import CoarseDeGiorgi.Localization.Assembly

/-! # The annular and inner-cube instances of compact localization

All cubes and partitions are chosen from the radii alone, before the function.
The general cutoff estimate is `exists_localization_sum_constant`.
-/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization Set MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

/-- Properties of the finite cover needed in the source localization argument. -/
def LocalizationCover (m : ℤ) (K : Set (Vec d)) (R δ : ℝ) : Prop :=
  (∀ z ∈ coverIndices m K,
    IsCompact (closure (auxCube m z)) ∧ closure (auxCube m z) ⊆ radiusCube R) ∧
  ((coverIndices m K).card : ℝ) ≤ (960 : ℝ) ^ d * δ ^ (-(d : ℝ)) ∧
  (∀ x : Vec d, ((coverIndices m K).filter fun z => x ∈ closedAuxCube m z).card ≤ 4 ^ d) ∧
  ∃ U : Set (Vec d), IsOpen U ∧ K ⊆ U ∧
    ∀ x ∈ U, (∑ z ∈ coverIndices m K, localizationPartition m (coverIndices m K) z x) = 1

theorem localizationCover_of_coordinate_bounds {m : ℤ} {K : Set (Vec d)} {a R δ : ℝ}
    (hδ : 0 < δ) (hs1 : gridSpacing m ≤ 1) (hs : δ / 192 < gridSpacing m)
    (hK : ∀ y ∈ K, ∀ i, |y i| ≤ a / 2) (ha : a ≤ 1)
    (hm : a + 4 * gridSpacing m < R) : LocalizationCover m K R δ := by
  refine ⟨fun _ hz => selected_auxCube_compactly_contained hK hm hz,
    card_coverIndices_le_gap hδ hs1 hs K, card_filter_closedAuxCube_le m (coverIndices m K), ?_⟩
  apply exists_open_partition_neighborhood hs1
  intro y hy i
  exact (hK y hy i).trans (by linarith only [ha])

/-- The same construction for the closed inner cube. -/
theorem exists_inner_localization_cover {ρ R : ℝ} (hρ : 1 / 2 ≤ ρ)
    (hρR : ρ < R) (hR : R ≤ 1) :
    ∃ m : ℤ, 0 ≤ m ∧ (R - ρ) / 192 < gridSpacing m ∧
      gridSpacing m ≤ (R - ρ) / 64 ∧
      LocalizationCover m {x : Vec d | ∀ i, |x i| ≤ ρ / 2} R (R - ρ) := by
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  obtain ⟨m, hm0, hslo, hshi⟩ := exists_localization_scale hδ (by linarith only [hρ, hR])
  refine ⟨m, hm0, hslo, hshi, ?_⟩
  exact localizationCover_of_coordinate_bounds hδ (by linarith only [hshi, hρ, hR]) hslo
    (fun _ hx => hx) (hρR.le.trans hR) (inner_margin hρR hshi)

/-- Every surface radius in the source interval lies in the partition neighborhood. -/
theorem mem_localizationAnnulus_of_radius {ρ R τ : ℝ} (hρR : ρ < R)
    (hτlo : ρ + (R - ρ) / 4 < τ) (hτhi : τ < ρ + (R - ρ) / 2)
    {x : Vec d} (hx : 2 * ‖x‖ = τ) : x ∈ localizationAnnulus ρ R := by
  constructor <;> rw [hx] <;> linarith only [hρR, hτlo, hτhi]

/-- The localized function agrees with the original on the open neighborhood. -/
theorem localizedFunction_eq_on_neighborhood {m : ℤ} {K : Set (Vec d)} {R δ : ℝ}
    (hcover : LocalizationCover m K R δ) (w : Vec d → ℝ) :
    ∃ U : Set (Vec d), IsOpen U ∧ K ⊆ U ∧
      EqOn (localizedFunction m (coverIndices m K) w) w U := by
  obtain ⟨U, hU, hKU, hsum⟩ := hcover.2.2.2
  refine ⟨U, hU, hKU, fun x hx => ?_⟩
  exact localizedFunction_eq_on_partition (hsum x hx) w

/-- Zero extension has compact support in the outer open cube even for a merely
measurable input: the smooth partition supplies all support control. -/
theorem localizedFunction_compactly_supported {m : ℤ} {K : Set (Vec d)} {R δ : ℝ}
    (hcover : LocalizationCover m K R δ) (w : Vec d → ℝ) :
    HasCompactSupport (localizedFunction m (coverIndices m K) w) ∧
      tsupport (localizedFunction m (coverIndices m K) w) ⊆ radiusCube R := by
  let B : Set (Vec d) := ⋃ z ∈ coverIndices m K, closure (auxCube m z)
  have hBc : IsCompact B := (coverIndices m K).isCompact_biUnion fun z hz => (hcover.1 z hz).1
  have hsupp : Function.support (localizedFunction m (coverIndices m K) w) ⊆ B := by
    intro x hx
    by_contra hxB
    have hzero (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) :
        localizationPartition m (coverIndices m K) z x = 0 := by
      by_contra hn
      have hxQ := support_partition_subset_auxCube m (coverIndices m K) z hn
      exact hxB (mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨hz, subset_closure hxQ⟩⟩)
    have hh : localizedFunction m (coverIndices m K) w x = 0 := by
      unfold localizedFunction
      apply Finset.sum_eq_zero
      intro z hz
      rw [hzero z hz, zero_mul]
    exact hx hh
  have hts : tsupport (localizedFunction m (coverIndices m K) w) ⊆ B :=
    closure_minimal hsupp hBc.isClosed
  refine ⟨hBc.of_isClosed_subset isClosed_closure hts, ?_⟩
  intro x hx
  obtain ⟨z, hz, hxQ⟩ := mem_iUnion₂.mp (hts hx)
  exact (hcover.1 z hz).2 hxQ

/-- Replacing the selected grid spacing by the radius gap in (e.localization.sum).
The constant is chosen before the gap, grid level, cover, and function. -/
theorem exists_localization_sum_gap_constant [NeZero d] {α r : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hr : 1 < r) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ 0 < C ∧
      ∀ (δ : ℝ), 0 < δ → ∀ (m : ℤ), gridSpacing m ≤ 1 →
      δ / 192 < gridSpacing m → ∀ (Z : Finset (Fin d → ℤ)) (w : Vec d → ℝ),
      Measurable w → (∀ z ∈ Z, fracNorm (auxCube m z) α r w < ⊤) →
      fracNorm univ α r (localizedFunction m Z w) ^ r ≤
        C * (∑ z ∈ Z, fracSeminorm (auxCube m z) α r w ^ r) +
          C * ENNReal.ofReal (δ ^ (-α * r)) *
            ∑ z ∈ Z, MeasureTheory.eLpNorm w (ENNReal.ofReal r)
              (MeasureTheory.volume.restrict (auxCube m z)) ^ r := by
  obtain ⟨A, hAfin, hApos, hsum⟩ := exists_localization_sum_constant (d := d) hα0 hα1 hr
  let B : ℝ≥0∞ := ENNReal.ofReal ((192 : ℝ) ^ (α * r))
  let C : ℝ≥0∞ := A * (1 + B)
  refine ⟨C, by dsimp [C, B]; finiteness, by dsimp [C]; positivity, ?_⟩
  intro δ hδ m hs1 hs Z w hw hfin
  have hscale : gridSpacing m ^ (-α * r) ≤ (192 : ℝ) ^ (α * r) * δ ^ (-α * r) := by
    have hh := Real.rpow_le_rpow_of_nonpos (show 0 < δ / 192 by positivity) hs.le
      (show -α * r ≤ 0 by nlinarith only [hα0, hr])
    apply hh.trans_eq
    rw [Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 192),
      show -α * r = -(α * r) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 192),
      div_inv_eq_mul]
    exact mul_comm _ _
  have hAs : A ≤ C := by dsimp [C]; exact le_mul_of_one_le_right' (le_add_right le_rfl)
  have hAB : A * B ≤ C := by dsimp [C]; exact mul_le_mul_right (le_add_left le_rfl) A
  apply (hsum m hs1 Z w hw hfin).trans
  apply add_le_add
  · simpa only [mul_comm] using mul_le_mul_right hAs
      (∑ z ∈ Z, fracSeminorm (auxCube m z) α r w ^ r)
  · have hscaled := ENNReal.ofReal_le_ofReal hscale
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 192) _)] at hscaled
    have hcoef : A * ENNReal.ofReal (gridSpacing m ^ (-α * r)) ≤
        C * ENNReal.ofReal (δ ^ (-α * r)) := by
      calc
        _ ≤ A * (B * ENNReal.ofReal (δ ^ (-α * r))) := mul_le_mul_right hscaled A
        _ ≤ _ := by
          simpa only [mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_right hAB (ENNReal.ofReal (δ ^ (-α * r)))
    simpa only [mul_comm] using mul_le_mul_right hcoef
      (∑ z ∈ Z, MeasureTheory.eLpNorm w (ENNReal.ofReal r)
        (MeasureTheory.volume.restrict (auxCube m z)) ^ r)

end
end CoarseDeGiorgi.Localization
