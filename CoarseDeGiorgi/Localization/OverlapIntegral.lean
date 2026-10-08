import CoarseDeGiorgi.Localization.SparseSum
import CoarseDeGiorgi.Localization.Geometry
import CoarseDeGiorgi.Statements.WeightedEnergy

/-! # Bounded-overlap integrals and the finite-sum energy loss -/
namespace CoarseDeGiorgi.Localization
open Homogenization MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι : Type*} {d : ℕ}

/-- Integrate the pointwise multiplicity, keeping zero times infinity meaningful. -/
theorem sum_lintegral_restrict_le_of_overlap (S : Finset ι) (Q : ι → Set (Vec d))
    {U : Set (Vec d)} (hQ : ∀ i ∈ S, MeasurableSet (Q i)) (hU : MeasurableSet U)
    (hsub : ∀ i ∈ S, Q i ⊆ U) {M : ℕ}
    (hM : ∀ x, (S.filter fun i => x ∈ Q i).card ≤ M)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) :
    (∑ i ∈ S, ∫⁻ x in Q i, f x) ≤ (M : ℝ≥0∞) * ∫⁻ x in U, f x := by
  have hpoint (x : Vec d) : (∑ i ∈ S, (Q i).indicator f x) ≤ (M : ℝ≥0∞) * U.indicator f x := by
    have he : (∑ i ∈ S, (Q i).indicator f x) =
        ((S.filter fun i => x ∈ Q i).card : ℝ≥0∞) * f x := by
      simp only [indicator_apply]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    by_cases hx : x ∈ U
    · rw [he, indicator_of_mem hx]
      have hc : ((S.filter fun i => x ∈ Q i).card : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by exact_mod_cast hM x
      simpa only [mul_comm] using mul_le_mul_right hc (f x)
    · rw [indicator_of_notMem hx, mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro i hi
      exact indicator_of_notMem (fun h => hx (hsub i hi h)) f
  calc
    _ = ∫⁻ x, ∑ i ∈ S, (Q i).indicator f x := by
      rw [lintegral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        exact (lintegral_indicator (hQ i hi) f).symm
      · intro i hi
        exact hf.indicator (hQ i hi)
    _ ≤ ∫⁻ x, (M : ℝ≥0∞) * U.indicator f x := lintegral_mono hpoint
    _ = _ := by rw [lintegral_const_mul' _ _ (by finiteness), lintegral_indicator hU]

/-- The source finite-sum Hölder inequality, including infinite energies. -/
theorem sum_rpow_le_card_rpow_mul_sum_rpow {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (S : Finset ι) (E : ι → ℝ≥0∞) :
    (∑ i ∈ S, E i ^ θ) ≤ (S.card : ℝ≥0∞) ^ (1 - θ) * (∑ i ∈ S, E i) ^ θ := by
  have hp := Real.HolderConjugate.inv_one_sub_inv hθ hθ1
  have hh := ENNReal.inner_le_Lp_mul_Lq S (fun i => E i ^ θ) (fun _ => (1 : ℝ≥0∞)) hp
  simp only [mul_one, ← ENNReal.rpow_mul, mul_inv_cancel₀ hθ.ne', ENNReal.rpow_one,
    one_div, inv_inv, ENNReal.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
  simpa only [mul_comm] using hh

/-- Bound the sum of local powers by global mass and the cover cardinality. -/
theorem sum_local_energy_rpow_le {m : ℤ} {K : Set (Vec d)} {a R θ : ℝ}
    (hK : ∀ y ∈ K, ∀ i, |y i| ≤ a / 2) (hm : a + 4 * gridSpacing m < R)
    (hθ : 0 < θ) (hθ1 : θ < 1) {e : Vec d → ℝ≥0∞} (he : Measurable e) :
    (∑ z ∈ coverIndices m K, (∫⁻ x in auxCube m z, e x) ^ θ) ≤
      ((coverIndices m K).card : ℝ≥0∞) ^ (1 - θ) *
        ((4 ^ d : ℕ) : ℝ≥0∞) ^ θ * (∫⁻ x in radiusCube R, e x) ^ θ := by
  have hsub (z : Fin d → ℤ) (hz : z ∈ coverIndices m K) : auxCube m z ⊆ radiusCube R :=
    (auxCube_subset_closedAuxCube m z).trans (selected_closedAuxCube_subset hK hm hz)
  have hU : MeasurableSet (radiusCube (d := d) R) := by
    apply IsOpen.measurableSet
    simp only [radiusCube, ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i |>.abs) continuous_const
  have hmass := sum_lintegral_restrict_le_of_overlap (coverIndices m K) (auxCube m)
    (fun z _ => (isOpen_auxCube m z).measurableSet) hU hsub
    (fun x => le_trans (Finset.card_le_card (by
      intro z hz
      obtain ⟨hzZ, hx⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzZ, auxCube_subset_closedAuxCube m z hx⟩))
      (card_filter_closedAuxCube_le m (coverIndices m K) x)) he
  calc
    _ ≤ ((coverIndices m K).card : ℝ≥0∞) ^ (1 - θ) *
        (∑ z ∈ coverIndices m K, ∫⁻ x in auxCube m z, e x) ^ θ :=
      sum_rpow_le_card_rpow_mul_sum_rpow hθ hθ1 _ _
    _ ≤ ((coverIndices m K).card : ℝ≥0∞) ^ (1 - θ) *
        (((4 ^ d : ℕ) : ℝ≥0∞) * ∫⁻ x in radiusCube R, e x) ^ θ :=
      mul_le_mul_right (ENNReal.rpow_le_rpow hmass hθ.le) _
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.le, mul_assoc]

end
end CoarseDeGiorgi.Localization
