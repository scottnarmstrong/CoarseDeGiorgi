import CoarseDeGiorgi.Weighted.Defs
import CoarseDeGiorgi.Foundations.QuadraticForm
import Homogenization.CoarseGraining.QuadraticStability.Integral

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Measurability of the coefficient flux. -/
theorem flux_aestronglyMeasurable (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V)) :
    AEStronglyMeasurable (fun x => matVecMul (a x) (G x)) (volume.restrict V) := by
  have hc : Continuous (fun p : Mat d × Vec d => matVecMul p.1 p.2) := by
    unfold matVecMul
    fun_prop
  exact hc.comp_aestronglyMeasurable (ha.1.prodMk hG)

/-- The nonnegative quadratic energy density is measurable. -/
theorem quadratic_aestronglyMeasurable (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V)) :
    AEStronglyMeasurable (fun x => vecDot (G x) (matVecMul (a x) (G x)))
      (volume.restrict V) := by
  have hc : Continuous (fun p : Vec d × Vec d => vecDot p.1 p.2) := by
    unfold vecDot
    fun_prop
  exact hc.comp_aestronglyMeasurable (hG.prodMk (flux_aestronglyMeasurable ha hG))

/-- Positivity of the quadratic energy density. -/
theorem quadratic_nonneg (ha : IsWeightedCoeffOn V a) (G : Vec d → Vec d) :
    0 ≤ᵐ[volume.restrict V] fun x => vecDot (G x) (matVecMul (a x) (G x)) := by
  filter_upwards [ha.2.1] with x hx
  simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
    hx.posSemidef.dotProduct_mulVec_nonneg (x := G x)

/-- Finite extended energy gives an integrable real quadratic density. -/
theorem quadratic_integrable (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hE : weightedEnergy a V G < ⊤) :
    IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) V :=
  (lintegral_ofReal_ne_top_iff_integrable
    (quadratic_aestronglyMeasurable ha hG) (quadratic_nonneg ha G)).mp hE.ne

/-- Conversion of finite weighted energy to its real integral. -/
theorem energy_toReal (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V)) :
    (weightedEnergy a V G).toReal =
      ∫ x in V, vecDot (G x) (matVecMul (a x) (G x)) :=
  (integral_eq_lintegral_of_nonneg_ae (quadratic_nonneg ha G)
    (quadratic_aestronglyMeasurable ha hG)).symm

/-- The square-root product occurring in Cauchy–Schwarz is integrable. -/
theorem sqrt_mul_sqrt_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    Integrable (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ := by
  refine ((hf.add hg).div_const 2).mono'
    ((Real.continuous_sqrt.comp_aestronglyMeasurable hf.1).mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg.1)) ?_
  filter_upwards [hf0, hg0] with x hx hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  exact sqrt_mul_sqrt_le_half_add hx hy

/-- Scalar trace domination gives the Euclidean L¹ bound. -/
theorem length_integrable_and_bound {G : Vec d → Vec d} {t : Vec d → ℝ}
    (ha : IsWeightedCoeffOn V a)
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hE : weightedEnergy a V G < ⊤) (ht : IntegrableOn t V)
    (ht0 : 0 ≤ᵐ[volume.restrict V] t)
    {H : Vec d → Vec d} (hH : AEStronglyMeasurable H (volume.restrict V))
    (hbound : ∀ᵐ x ∂(volume.restrict V),
      vecDot (H x) (H x) ≤ t x * vecDot (G x) (matVecMul (a x) (G x))) :
    IntegrableOn (fun x => Real.sqrt (vecDot (H x) (H x))) V ∧
      (∫ x in V, Real.sqrt (vecDot (H x) (H x))) ≤
        Real.sqrt (∫ x in V, t x) * Real.sqrt (weightedEnergy a V G).toReal := by
  classical
  have hq := quadratic_integrable ha hG hE
  have hq0 := quadratic_nonneg ha G
  have hprod := sqrt_mul_sqrt_integrable ht hq ht0 hq0
  have hlen : AEStronglyMeasurable (fun x => Real.sqrt (vecDot (H x) (H x)))
      (volume.restrict V) := by
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    have hc : Continuous (fun z : Vec d => vecDot z z) := by
      unfold vecDot
      fun_prop
    exact hc.comp_aestronglyMeasurable hH
  have hle : ∀ᵐ x ∂(volume.restrict V), Real.sqrt (vecDot (H x) (H x)) ≤
      Real.sqrt (t x) * Real.sqrt (vecDot (G x) (matVecMul (a x) (G x))) := by
    filter_upwards [hbound, ht0] with x hx htx
    exact (Real.sqrt_le_sqrt hx).trans_eq (Real.sqrt_mul htx _)
  have hint : IntegrableOn (fun x => Real.sqrt (vecDot (H x) (H x))) V := by
    refine hprod.mono' hlen ?_
    filter_upwards [hle] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hx
  refine ⟨hint, (integral_mono_ae hint hprod hle).trans ?_⟩
  rw [energy_toReal ha hG]
  exact integral_sqrt_mul_sqrt_le ht hq ht0 hq0

/-- Gradient length estimate, for every measurable finite-energy field. -/
theorem gradient_length_integrable_and_bound (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hE : weightedEnergy a V G < ⊤) :
    IntegrableOn (fun x => Real.sqrt (vecDot (G x) (G x))) V ∧
      (∫ x in V, Real.sqrt (vecDot (G x) (G x))) ≤
        Real.sqrt (∫ x in V, ((a x)⁻¹).trace) * Real.sqrt (weightedEnergy a V G).toReal := by
  refine length_integrable_and_bound ha hG hE ha.2.2.2 ?_ hG ?_
  · filter_upwards [ha.2.1] with x hx
    exact hx.inv.posSemidef.trace_nonneg
  · filter_upwards [ha.2.1] with x hx
    exact Foundations.vecDot_self_le_inv_trace_mul_quadratic (a x) hx (G x)

/-- Flux length estimate, for every measurable finite-energy field. -/
theorem flux_length_integrable_and_bound (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hE : weightedEnergy a V G < ⊤) :
    IntegrableOn (fun x => Real.sqrt
      (vecDot (matVecMul (a x) (G x)) (matVecMul (a x) (G x)))) V ∧
      (∫ x in V, Real.sqrt
        (vecDot (matVecMul (a x) (G x)) (matVecMul (a x) (G x)))) ≤
        Real.sqrt (∫ x in V, (a x).trace) * Real.sqrt (weightedEnergy a V G).toReal := by
  refine length_integrable_and_bound ha hG hE ha.2.2.1 ?_ (flux_aestronglyMeasurable ha hG) ?_
  · filter_upwards [ha.2.1] with x hx
    exact hx.posSemidef.trace_nonneg
  · filter_upwards [ha.2.1] with x hx
    exact Foundations.vecDot_matVecMul_self_le_trace_mul_quadratic (a x) hx (G x)

/-- Coordinate integrability follows from the Euclidean length estimate. -/
theorem coord_integrable_of_length {H : Vec d → Vec d}
    (hH : AEStronglyMeasurable H (volume.restrict V))
    (hL : IntegrableOn (fun x => Real.sqrt (vecDot (H x) (H x))) V) (i : Fin d) :
    IntegrableOn (fun x => H x i) V := by
  refine hL.mono' ((continuous_apply i).comp_aestronglyMeasurable hH) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_apply_le_vecNormSq (H x) i)

/-- Two finite-energy fields have finite-energy sum. -/
theorem energy_add_lt_top (ha : IsWeightedCoeffOn V a)
    {G H : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hH : AEStronglyMeasurable H (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) (hEH : weightedEnergy a V H < ⊤) :
    weightedEnergy a V (G + H) < ⊤ := by
  have hpos (A : Mat d) (hA : A.PosDef) (z : Vec d) :
      0 ≤ vecDot z (matVecMul A z) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using
      hA.posSemidef.dotProduct_mulVec_nonneg (x := z)
  have hqG := quadratic_integrable ha hG hEG
  have hqH := quadratic_integrable ha hH hEH
  have hqsum : IntegrableOn
      (fun x => vecDot ((G + H) x) (matVecMul (a x) ((G + H) x))) V := by
    refine ((hqG.add hqH).const_mul 2).mono'
      (quadratic_aestronglyMeasurable ha (hG.add hH)) ?_
    filter_upwards [ha.2.1] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos _ hx _)]
    have hdiff := hpos (a x) hx (G x - H x)
    have hcomm : vecDot (H x) (matVecMul (a x) (G x)) =
        vecDot (G x) (matVecMul (a x) (H x)) :=
      vecDot_matVecMul_comm_of_isSymm (by simpa [Matrix.IsSymm, Matrix.IsHermitian] using hx.1) _ _
    simp only [Pi.add_apply, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
      vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hcomm] at hdiff ⊢
    linarith only [hdiff]
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
    (quadratic_aestronglyMeasurable ha (hG.add hH)) (quadratic_nonneg ha (G + H))).mpr hqsum)

/-- Negating a gradient does not change its energy. -/
theorem energy_neg (G : Vec d → Vec d) : weightedEnergy a V (-G) = weightedEnergy a V G := by
  unfold weightedEnergy CoarseDeGiorgi.weightedEnergy
  simp only [Pi.neg_apply, matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]

/-- Integral Cauchy–Schwarz for arbitrary measurable finite-energy fields. -/
theorem pairing_integrable_and_bound (ha : IsWeightedCoeffOn V a)
    {G H : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (volume.restrict V))
    (hH : AEStronglyMeasurable H (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) (hEH : weightedEnergy a V H < ⊤) :
    IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (H x))) V ∧
      |∫ x in V, vecDot (G x) (matVecMul (a x) (H x))| ≤
        Real.sqrt (weightedEnergy a V G).toReal * Real.sqrt (weightedEnergy a V H).toReal := by
  have hqG := quadratic_integrable ha hG hEG
  have hqH := quadratic_integrable ha hH hEH
  have h0G := quadratic_nonneg ha G
  have h0H := quadratic_nonneg ha H
  have hprod := sqrt_mul_sqrt_integrable hqG hqH h0G h0H
  have hc : Continuous (fun p : Vec d × Vec d => vecDot p.1 p.2) := by
    unfold vecDot
    fun_prop
  have hmeas := hc.comp_aestronglyMeasurable (hG.prodMk (flux_aestronglyMeasurable ha hH))
  have hbound : ∀ᵐ x ∂(volume.restrict V),
      |vecDot (G x) (matVecMul (a x) (H x))| ≤
        Real.sqrt (vecDot (G x) (matVecMul (a x) (G x))) *
        Real.sqrt (vecDot (H x) (matVecMul (a x) (H x))) := by
    filter_upwards [ha.2.1, h0G] with x hx hzero
    have hcs := hx.star_dotProduct_mulVec_mul_le (G x) (H x)
    have hcs' : vecDot (G x) (matVecMul (a x) (H x)) ^ 2 ≤
        vecDot (G x) (matVecMul (a x) (G x)) * vecDot (H x) (matVecMul (a x) (H x)) := by
      simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec, pow_two] using hcs
    rw [← Real.sqrt_sq_eq_abs]
    exact (Real.sqrt_le_sqrt hcs').trans_eq (Real.sqrt_mul hzero _)
  have hint : IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (H x))) V :=
    hprod.mono' hmeas (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hint, ?_⟩
  calc
    |∫ x in V, vecDot (G x) (matVecMul (a x) (H x))| ≤
        ∫ x in V, |vecDot (G x) (matVecMul (a x) (H x))| := abs_integral_le_integral_abs
    _ ≤ ∫ x in V, Real.sqrt (vecDot (G x) (matVecMul (a x) (G x))) *
        Real.sqrt (vecDot (H x) (matVecMul (a x) (H x))) := integral_mono_ae hint.abs hprod hbound
    _ ≤ Real.sqrt (weightedEnergy a V G).toReal * Real.sqrt (weightedEnergy a V H).toReal := by
      rw [energy_toReal ha hG, energy_toReal ha hH]
      exact integral_sqrt_mul_sqrt_le hqG hqH h0G h0H

end CoarseDeGiorgi.Weighted
