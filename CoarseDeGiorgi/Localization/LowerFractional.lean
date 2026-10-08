import CoarseDeGiorgi.Localization.Assembly
import CoarseDeGiorgi.Localization.OverlapIntegral

/-! # Local mass control for localization covers

The finite-overlap estimate bounds the sum of local Lʳ masses on a cover by
the mass on a containing cube.
-/
namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable


/-- The mass part of localization also uses the proved overlap, not the cover size. -/
theorem sum_local_eLpNorm_rpow_le {r : ℝ} (hr : 0 < r)
    {m : ℤ} {K : Set (Vec d)} {a R : ℝ}
    (hK : ∀ y ∈ K, ∀ i, |y i| ≤ a / 2) (hm : a + 4 * gridSpacing m < R)
    {w : Vec d → ℝ} (hw : Measurable w) :
    (∑ z ∈ coverIndices m K, eLpNorm w (ENNReal.ofReal r) (volume.restrict (auxCube m z)) ^ r) ≤
      ((4 ^ d : ℕ) : ℝ≥0∞) * eLpNorm w (ENNReal.ofReal r) (volume.restrict (radiusCube R)) ^ r := by
  have hU : MeasurableSet (radiusCube (d := d) R) := by
    apply IsOpen.measurableSet
    simp only [radiusCube, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i |>.abs) continuous_const
  have hsub (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) : auxCube m z ⊆ radiusCube R :=
    (auxCube_subset_closedAuxCube m z).trans (selected_closedAuxCube_subset hK hm hz)
  have hM (x : Vec d) : ((coverIndices m K).filter fun z => x ∈ auxCube m z).card ≤ 4 ^ d :=
    le_trans (Finset.card_le_card (by
      intro z hz
      obtain ⟨hzZ, hx⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzZ, auxCube_subset_closedAuxCube m z hx⟩))
      (card_filter_closedAuxCube_le m (coverIndices m K) x)
  have hpower : Measurable (fun x => ENNReal.ofReal (|w x| ^ r)) := by
    simpa only [Real.norm_eq_abs] using (hw.norm.pow measurable_const).ennreal_ofReal
  have hh := sum_lintegral_restrict_le_of_overlap (coverIndices m K) (auxCube m)
    (fun z _ => (isOpen_auxCube m z).measurableSet) hU hsub hM hpower
  have hnorm (V : Set (Vec d)) (hV : MeasurableSet V) :
      (∫⁻ x in V, ENNReal.ofReal (|w x| ^ r)) = eLpNorm w (ENNReal.ofReal r) (volume.restrict V) ^ r := by
    simpa only [CoarseDeGiorgi.Foundations.FracGeometry.cutoffMass,
      lintegral_indicator hV] using CoarseDeGiorgi.Foundations.FracGeometry.lintegral_cutoffMass hV hr
        hw.aestronglyMeasurable.restrict
  simp_rw [hnorm _ (isOpen_auxCube m _).measurableSet] at hh
  rw [hnorm _ hU] at hh
  exact hh


end
end CoarseDeGiorgi.Localization
