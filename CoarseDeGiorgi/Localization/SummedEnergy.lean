module

public import CoarseDeGiorgi.Localization.OverlapIntegral
public import CoarseDeGiorgi.Weighted.Energy
public import CoarseDeGiorgi.Statements.IsWeightedCoeffOn

/-! # Bounded overlap of the local energies

The sum over the cover of the energies on the cubes is at most `4^d` times the energy on a
containing cube (exponent one, so no loss from the number of cubes). -/

@[expose] public section

namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

theorem sum_energy_overlap_le {V : Set (Vec d)} {a : CoeffField d}
    (ha : IsWeightedCoeffOn V a) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict V))
    {m : ℤ} {K : Set (Vec d)} {b R : ℝ} (hK : ∀ y ∈ K, ∀ i, |y i| ≤ b / 2)
    (hm : b + 4 * gridSpacing m < R) (hRV : radiusCube R ⊆ V) :
    (∑ z ∈ coverIndices m K, weightedEnergy a (auxCube m z) G) ≤
      ((4 ^ d : ℕ) : ℝ≥0∞) * weightedEnergy a (radiusCube R) G := by
  have hdens := (Weighted.quadratic_aestronglyMeasurable ha hG).aemeasurable.ennreal_ofReal
  have hdensR : AEMeasurable (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))))
      (volume.restrict (radiusCube R)) := hdens.mono_set hRV
  have hsub (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) : auxCube m z ⊆ radiusCube R :=
    (auxCube_subset_closedAuxCube m z).trans (selected_closedAuxCube_subset hK hm hz)
  have hU : MeasurableSet (radiusCube (d := d) R) := by
    apply IsOpen.measurableSet
    simp only [radiusCube, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i |>.abs) continuous_const
  set f := fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))) with hf
  have hmk := hdensR.measurable_mk
  have heq (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) :
      weightedEnergy a (auxCube m z) G = ∫⁻ x in auxCube m z, hdensR.mk f x :=
    lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset (hsub z hz) hdensR.ae_eq_mk)
  have heqR : weightedEnergy a (radiusCube R) G = ∫⁻ x in radiusCube R, hdensR.mk f x :=
    lintegral_congr_ae hdensR.ae_eq_mk
  rw [heqR, Finset.sum_congr rfl heq]
  exact sum_lintegral_restrict_le_of_overlap (coverIndices m K) (auxCube m)
    (fun z _ => (isOpen_auxCube m z).measurableSet) hU hsub
    (fun x => le_trans (Finset.card_le_card (by
      intro z hz
      obtain ⟨hzZ, hx⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzZ, auxCube_subset_closedAuxCube m z hx⟩))
      (card_filter_closedAuxCube_le m (coverIndices m K) x)) hmk

end
end CoarseDeGiorgi.Localization
