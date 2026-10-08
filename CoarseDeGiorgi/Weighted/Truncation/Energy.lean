import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Weighted.GraphRepresentation
import CoarseDeGiorgi.Foundations.ChainRule.LevelSets
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A bounded scalar multiplier bounds the literal weighted energy. -/
theorem energy_mul_le (ha : IsWeightedCoeffOn V a) {G : Vec d → Vec d}
    {b : Vec d → ℝ} {M : ℝ} (hb : ∀ᵐ x ∂volume.restrict V, |b x| ≤ M) :
    weightedEnergy a V (fun x => b x • G x) ≤
      ENNReal.ofReal (M ^ 2) * weightedEnergy a V G := by
  change (∫⁻ x in V, ENNReal.ofReal (vecDot (b x • G x)
    (matVecMul (a x) (b x • G x)))) ≤ _
  simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  change _ ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ x in V,
    ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hb, quadratic_nonneg ha G] with x hx hq
  rw [← ENNReal.ofReal_mul (sq_nonneg M)]
  apply ENNReal.ofReal_le_ofReal
  have hs : b x ^ 2 ≤ M ^ 2 := by
    have hm := (abs_nonneg (b x)).trans hx
    nlinarith only [hx, hm, sq_abs (b x), abs_nonneg (b x)]
  nlinarith only [mul_le_mul_of_nonneg_right hs hq]

/-- Dominated convergence of bounded scalar factors in the weighted energy. -/
theorem tendsto_energy_mul_zero (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hE : weightedEnergy a V G < ⊤) {b : ℕ → Vec d → ℝ} {M : ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict V))
    (hbound : ∀ n, ∀ᵐ x ∂volume.restrict V, |b n x| ≤ M)
    (ht : ∀ᵐ x ∂volume.restrict V, Tendsto (fun n => b n x) atTop (𝓝 0)) :
    Tendsto (fun n => weightedEnergy a V (fun x => b n x • G x)) atTop (𝓝 0) := by
  let q := fun x => vecDot (G x) (matVecMul (a x) (G x))
  let B := fun x => ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (q x)
  have hfin : (∫⁻ x in V, B x) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne
  have hmeas (n : ℕ) : AEMeasurable
      (fun x => ENNReal.ofReal (vecDot (b n x • G x)
        (matVecMul (a x) (b n x • G x)))) (volume.restrict V) :=
    (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      (quadratic_aestronglyMeasurable ha ((hb n).smul hG))).aemeasurable
  have hdom (n : ℕ) : ∀ᵐ x ∂volume.restrict V,
      ENNReal.ofReal (vecDot (b n x • G x)
        (matVecMul (a x) (b n x • G x))) ≤ B x := by
    filter_upwards [hbound n, quadratic_nonneg ha G] with x hx hq
    dsimp [B, q]
    simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    rw [← ENNReal.ofReal_mul (sq_nonneg M)]
    apply ENNReal.ofReal_le_ofReal
    have hm := (abs_nonneg (b n x)).trans hx
    have hs : b n x ^ 2 ≤ M ^ 2 := by
      nlinarith only [hx, hm, sq_abs (b n x), abs_nonneg (b n x)]
    nlinarith only [mul_le_mul_of_nonneg_right hs hq]
  have hlim : ∀ᵐ x ∂volume.restrict V, Tendsto
      (fun n => ENNReal.ofReal (vecDot (b n x • G x)
        (matVecMul (a x) (b n x • G x)))) atTop (𝓝 0) := by
    filter_upwards [ht] with x hx
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hx.mul hx).mul_const (q x))
    simpa only [Function.comp_def, zero_mul, ENNReal.ofReal_zero,
      matVecMul_smul, vecDot_smul_left, vecDot_smul_right, mul_assoc, q] using hh
  simpa only [lintegral_zero, weightedEnergy, CoarseDeGiorgi.weightedEnergy] using
    tendsto_lintegral_of_dominated_convergence' B hmeas hdom hfin hlim

/-- The quadratic triangle bound in extended energy. -/
theorem energy_add_le (ha : IsWeightedCoeffOn V a) (G H : Vec d → Vec d)
    (hGM : AEStronglyMeasurable G (volume.restrict V)) :
    weightedEnergy a V (G + H) ≤ 2 * (weightedEnergy a V G + weightedEnergy a V H) := by
  change (∫⁻ x in V, ENNReal.ofReal (vecDot ((G + H) x)
    (matVecMul (a x) ((G + H) x)))) ≤ _
  change _ ≤ 2 * ((∫⁻ x in V, ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) +
    ∫⁻ x in V, ENNReal.ofReal (vecDot (H x) (matVecMul (a x) (H x))))
  rw [mul_add]
  rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ENNReal) ≠ ⊤),
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ENNReal) ≠ ⊤)]
  rw [← lintegral_add_left' ((ENNReal.continuous_ofReal.comp_aestronglyMeasurable
    (quadratic_aestronglyMeasurable ha hGM)).aemeasurable.const_mul 2)]
  apply lintegral_mono_ae
  filter_upwards [ha.2.1, quadratic_nonneg ha G, quadratic_nonneg ha H] with x hx hG hH
  have hd := hx.posSemidef.dotProduct_mulVec_nonneg (x := G x - H x)
  have hcomm : vecDot (H x) (matVecMul (a x) (G x)) =
      vecDot (G x) (matVecMul (a x) (H x)) :=
    vecDot_matVecMul_comm_of_isSymm
      (by simpa [Matrix.IsSymm, Matrix.IsHermitian] using hx.1) _ _
  have hd' : 0 ≤ vecDot (G x - H x) (matVecMul (a x) (G x - H x)) := by
    simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using hd
  rw [← show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) by norm_num]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hG) (mul_nonneg (by norm_num) hH)]
  apply ENNReal.ofReal_le_ofReal
  simp only [Pi.add_apply, sub_eq_add_neg, matVecMul_add, matVecMul_neg,
    vecDot_add_left, vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hcomm] at hd' ⊢
  linarith only [hd']

/-- Adding two fields tending to zero in energy preserves convergence. -/
theorem tendsto_energy_add_zero (ha : IsWeightedCoeffOn V a)
    {F H : ℕ → Vec d → Vec d}
    (hFM : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (hF : Tendsto (fun n => weightedEnergy a V (F n)) atTop (𝓝 0))
    (hH : Tendsto (fun n => weightedEnergy a V (H n)) atTop (𝓝 0)) :
    Tendsto (fun n => weightedEnergy a V (F n + H n)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => 2 * (weightedEnergy a V (F n) + weightedEnergy a V (H n)))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hF.add hH) (Or.inr (by norm_num : (2 : ENNReal) ≠ ⊤))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => bot_le) (fun n => energy_add_le ha (F n) (H n) (hFM n))

/-- The weighted level-set locality formula, by identification with W¹,¹. -/
theorem MemH1a.gradient_zero_on_level [NeZero d]
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) (c : ℝ) :
    {x | u x = c}.indicator G =ᵐ[volume.restrict V] (fun _ => 0) := by
  obtain ⟨hi, hGi, hw, _, _⟩ := memH1a_memW11 hV hne ha hu
  exact Foundations.grad_ae_zero_on_level_set_w11 hV
    (memLp_one_iff_integrable.mpr hi)
    (fun i => memLp_one_iff_integrable.mpr (hGi i)) hw c

end CoarseDeGiorgi.Weighted
