import CoarseDeGiorgi.Cubical.UpperSub
import CoarseDeGiorgi.Weighted.LowerSpecNorm
import CoarseDeGiorgi.Weighted.LowerSpecSup
import CoarseDeGiorgi.LowerFractional.Restriction
import CoarseDeGiorgi.Weighted.ResponseBoundsLower
import CoarseDeGiorgi.Statements.LowerResponseInv

/-! # Countable lower aggregation (quadratic form version) -/

namespace CoarseDeGiorgi.Cubical
open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

variable {d : ℕ}

/-- The quadratic form of an entrywise integrable matrix field is integrable. -/
lemma integrableOn_qf {U : Set (Vec d)} {A : Vec d → Mat d} (e : Vec d)
    (hA : ∀ i j, IntegrableOn (fun x => A x i j) U) :
    IntegrableOn (fun x => vecDot e (matVecMul (A x) e)) U := by
  unfold vecDot matVecMul
  refine integrable_finsetSum _ (fun i _ => ?_)
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ (fun j _ => ((hA i j).mul_const (e j)).const_mul (e i) |>.congr
    (Filter.Eventually.of_forall fun x => by ring))

theorem lower_quadratic_countable [NeZero d] {a : CoeffField d} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hU₀ : U.Nonempty) (ha : IsWeightedCoeffOn U a)
    {ι : Type} [Countable ι] (V : ι → Set (Vec d))
    (hV : ∀ i, IsOpenBoundedConvexDomain (V i)) (hV₀ : ∀ i, (V i).Nonempty)
    (haV : ∀ i, IsWeightedCoeffOn (V i) a)
    (hVU : ∀ i, V i ⊆ U) (hdisj : Pairwise (Function.onFun Disjoint V))
    (hcover : volume (U \ ⋃ i, V i) = 0) (e : Vec d) :
    Summable (fun i => (volume (V i)).toReal *
        qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e) ∧
      (volume U).toReal * qf (lowerResponseInv a U hU hU₀ ha) e ≤
        ∑' i, (volume (V i)).toReal *
          qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e := by
  classical
  have hvolU : 0 < (volume U).toReal :=
    ENNReal.toReal_pos (hU.isOpen.measure_pos volume hU₀).ne'
      hU.isBoundedDomain.isBounded.measure_lt_top.ne
  have hmeas : ∀ i, MeasurableSet (V i) := fun i => (hV i).isOpen.measurableSet
  have hUnion : (⋃ i, V i) ⊆ U := Set.iUnion_subset hVU
  have hvolV : ∀ i, 0 < (volume (V i)).toReal := fun i =>
    ENNReal.toReal_pos ((hV i).isOpen.measure_pos volume (hV₀ i)).ne'
      (hV i).isBoundedDomain.isBounded.measure_lt_top.ne
  -- summability
  have hinvU := Weighted.response_inverse_coefficient ha
  have hf : IntegrableOn (fun x => vecDot e (matVecMul ((a x)⁻¹) e)) U :=
    integrableOn_qf e (fun i j => Weighted.response_coefficient_entry_integrable hinvU i j)
  have hsumf := hasSum_integral_iUnion hmeas hdisj (hf.mono_set hUnion)
  have hsumm : Summable (fun i => (volume (V i)).toReal *
        qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e) := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsumf.summable
    · exact mul_nonneg (hvolV i).le
        (qf_nonneg (Weighted.LowerResponseImpl.lowerResponseInv_posDef (hV i) (hV₀ i) (haV i)).posSemidef e)
    · have hb := Weighted.LowerResponseImpl.lowerResponseInv_coefficient_bound (hV i) (hV₀ i) (haV i) e
      have : (volume (V i)).toReal * qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e ≤
          (volume (V i)).toReal * ((volume (V i)).toReal⁻¹ *
            ∫ x in V i, vecDot e (matVecMul ((a x)⁻¹) e)) :=
        mul_le_mul_of_nonneg_left hb (hvolV i).le
      rwa [← mul_assoc, mul_inv_cancel₀ (hvolV i).ne', one_mul] at this
  refine ⟨hsumm, ?_⟩
  -- the inequality
  have hsup := Weighted.LowerResponseImpl.lowerResponseInv_all_functions hU hU₀ ha e
  have hle : ((qf (lowerResponseInv a U hU hU₀ ha) e : ℝ) : EReal) ≤
      (((volume U).toReal⁻¹ * ∑' i, (volume (V i)).toReal *
          qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e : ℝ) : EReal) := by
    change ((vecDot e (matVecMul (Weighted.LowerResponseImpl.lowerResponseInv a U hU hU₀ ha) e) : ℝ) : EReal) ≤ _
    rw [hsup]
    refine iSup_le fun w => iSup_le fun G => iSup_le fun hw => ?_
    apply EReal.coe_le_coe_iff.mpr
    let obj : Vec d → ℝ := fun x => -vecDot (G x) (matVecMul (a x) (G x)) + 2 * vecDot e (G x)
    have hE : IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) U :=
      Weighted.quadratic_integrable ha hw.2.1 (Weighted.MemH1a.energy_lt_top hU.isOpen ha hw)
    have hG := Weighted.GradientCore.integrable ha (Weighted.memH1aEnergyField hU.isOpen ha hw)
    have hD : IntegrableOn (fun x => vecDot e (G x)) U := by
      change Integrable (fun x => vecDot e (G x)) (volume.restrict U)
      simpa only [Function.comp_def, Weighted.lowerDot_apply,
        Weighted.memH1aEnergyField_field] using (Weighted.lowerDot e).integrable_comp hG
    have hobj : IntegrableOn obj U := hE.neg.add (hD.const_mul 2)
    have hs := hasSum_integral_iUnion hmeas hdisj (hobj.mono_set hUnion)
    have hint : ∫ x in U, obj x = ∫ x in ⋃ i, V i, obj x :=
      setIntegral_congr_set (ae_eq_of_cover hUnion hcover)
    have hterm : ∀ i, ∫ x in V i, obj x ≤
        (volume (V i)).toReal * qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e := by
      intro i
      have hwi : Weighted.MemH1a a (V i) w G :=
        LowerFractional.memH1a_restrict hU hU₀ ha (hV i) (hVU i) hw
      have hsupi := Weighted.LowerResponseImpl.lowerResponseInv_all_functions (hV i) (hV₀ i) (haV i) e
      have hle' : ((volumeAverage (V i) obj : ℝ) : EReal) ≤
          ((qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e : ℝ) : EReal) := by
        change _ ≤ ((vecDot e (matVecMul (Weighted.LowerResponseImpl.lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e) : ℝ) : EReal)
        rw [hsupi]
        exact le_iSup_of_le w (le_iSup_of_le G (le_iSup_of_le hwi le_rfl))
      have h2 := EReal.coe_le_coe_iff.mp hle'
      have h3 := mul_le_mul_of_nonneg_left h2 (hvolV i).le
      unfold volumeAverage at h3
      rwa [← mul_assoc, mul_inv_cancel₀ (hvolV i).ne', one_mul] at h3
    have hineq : ∫ x in U, obj x ≤ ∑' i, (volume (V i)).toReal *
        qf (lowerResponseInv a (V i) (hV i) (hV₀ i) (haV i)) e := by
      rw [hint, ← hs.tsum_eq]
      exact Summable.tsum_le_tsum hterm hs.summable hsumm
    change (volume U).toReal⁻¹ * ∫ x in U, obj x ≤ _
    exact mul_le_mul_of_nonneg_left hineq (inv_nonneg.mpr hvolU.le)
  have := EReal.coe_le_coe_iff.mp hle
  have h2 := mul_le_mul_of_nonneg_left this hvolU.le
  rwa [← mul_assoc, mul_inv_cancel₀ hvolU.ne', one_mul] at h2

end CoarseDeGiorgi.Cubical
