import CoarseDeGiorgi.Cubical.LowerSub

/-! # Countable lower aggregation `e.lower.cube.aggregation` -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

theorem lower_aggregation_countable_main
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hU₀ : U.Nonempty) (ha : IsWeightedCoeffOn U a)
    {ι : Type} [Countable ι] (V : ι → Set (Vec d))
    (hV : ∀ i, IsOpenBoundedConvexDomain (V i)) (hV₀ : ∀ i, (V i).Nonempty)
    (haV : ∀ i, IsWeightedCoeffOn (V i) a)
    (hVU : ∀ i, V i ⊆ U) (hdisj : Pairwise (Function.onFun Disjoint V))
    (hcover : volume (U \ ⋃ i, V i) = 0) :
    Summable (fun i => ‖(((volume (V i)).toReal / (volume U).toReal : ℝ)) •
        lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)‖) ∧
    (∑' i, (((volume (V i)).toReal / (volume U).toReal : ℝ)) •
        lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i) -
      lowerResponseInv a U hU hU₀ ha).PosSemidef := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact psd_zero_dim _ _
  have : NeZero d := ⟨hd.ne'⟩
  have hvolU : 0 < (volume U).toReal :=
    ENNReal.toReal_pos (hU.isOpen.measure_pos volume hU₀).ne'
      hU.isBoundedDomain.isBounded.measure_lt_top.ne
  set N : ι → Mat d := fun i => (((volume (V i)).toReal / (volume U).toReal : ℝ)) •
        lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i) with hN
  have hvolpos : ∀ i, 0 ≤ (volume (V i)).toReal / (volume U).toReal := fun i =>
    div_nonneg ENNReal.toReal_nonneg hvolU.le
  have hNpsd : ∀ i, (N i).PosSemidef := fun i =>
    (Weighted.LowerResponseImpl.lowerResponseInv_posDef (hV i) (hV₀ i) (haV i)).posSemidef.smul (hvolpos i)
  have key := fun e => lower_quadratic_countable hU hU₀ ha V hV hV₀ haV hVU hdisj hcover e
  have hqN : ∀ e i, qf (N i) e = (volume U).toReal⁻¹ *
      ((volume (V i)).toReal * qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e) := by
    intro e i
    simp only [hN, qf_smul]; field_simp
  have hqs : ∀ e, Summable (fun i => qf (N i) e) := fun e => by
    simp only [hqN]; exact (key e).1.mul_left _
  refine psdSum N hNpsd hqs (lowerResponseInv a U hU hU₀ ha)
    (Weighted.LowerResponseImpl.lowerResponseInv_posDef hU hU₀ ha).posSemidef ?_
  intro e
  have h2 := mul_le_mul_of_nonneg_left (key e).2 (inv_nonneg.mpr hvolU.le)
  rw [← mul_assoc, inv_mul_cancel₀ hvolU.ne', one_mul] at h2
  have : ∑' i, qf (N i) e = (volume U).toReal⁻¹ * ∑' i, (volume (V i)).toReal *
      qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e := by
    simp only [hqN]; rw [tsum_mul_left]
  rw [this]; exact h2

end CoarseDeGiorgi.Cubical
