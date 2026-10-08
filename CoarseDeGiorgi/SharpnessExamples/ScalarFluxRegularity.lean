module

public import CoarseDeGiorgi.SharpnessExamples.ScalarFluxRadial

/-! # Derivative and Lipschitz bounds for the matched radial flux -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem scalarRadialFluxFactor_hasDerivAt_annulus {d : ℕ} (hd : 3 ≤ d)
    {n : ℕ} {ζ r : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hr : cylinderRadius d n ζ (cylinderRadialConstant d) < r) :
    HasDerivAt (scalarRadialFluxFactor d n ζ)
      (scalarRadialFluxFactor d n ζ r * (1 - (d : ℝ)) / r) r := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  let B := -cylinderRadialConstant d * scalarAnnulusValue d n ζ (cylinderRadialConstant d) / ε ^ 2
  let α := 1 - (d : ℝ)
  have hε : 0 < ε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have hr0 := hε.trans hr
  have hlocal : scalarRadialFluxFactor d n ζ =ᶠ[𝓝 r] fun t => B * Real.rpow (t / ε) α := by
    filter_upwards [eventually_gt_nhds hr] with t ht
    have h : 1 ≤ t / ε := (le_div_iff₀ hε).2 (by simpa only [one_mul] using ht.le)
    simp only [scalarRadialFluxFactor, max_eq_right h, B, ε, α]
  have hdv := ((Real.hasDerivAt_rpow_const (p := α) (Or.inl (div_pos hr0 hε).ne')).comp r
    ((hasDerivAt_id r).div_const ε)).const_mul B
  have heq : scalarRadialFluxFactor d n ζ r = B * Real.rpow (r / ε) α := hlocal.self_of_nhds
  apply HasDerivAt.congr_of_eventuallyEq _ hlocal
  convert hdv using 1
  · rfl
  · rw [heq]
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_sub_one (div_pos hr0 hε).ne']
    dsimp only [α]
    field_simp

theorem scalarRadialFluxFactor_nonpos {d : ℕ} (hd : 3 ≤ d)
    {n : ℕ} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ2 : ζ < 2) (r : ℝ) :
    scalarRadialFluxFactor d n ζ r ≤ 0 := by
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2
    (cylinderRadialConstant_pos hd)).1
  have ha : 0 ≤ scalarAnnulusValue d n ζ (cylinderRadialConstant d) := by
    unfold scalarAnnulusValue
    exact mul_nonneg (inv_nonneg.mpr (cylinderB_pos n).le) (Real.rpow_nonneg hε.le _)
  exact mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (cylinderRadialConstant_pos hd).le) ha)
      (sq_nonneg _)) (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

/-- Real multiplication by a constant is globally Lipschitz. -/
theorem real_const_mul_lipschitz (c : ℝ) :
    LipschitzWith ‖c‖₊ (fun r : ℝ => c * r) := by
  apply LipschitzWith.of_dist_le_mul
  intro r t
  simp only [Real.dist_eq, ← mul_sub, abs_mul, coe_nnnorm, Real.norm_eq_abs]
  exact le_rfl

private theorem negativePower_lipschitzOn {α : ℝ} (hα : α ≤ 0) :
    LipschitzOnWith ‖α‖₊ (fun r : ℝ => Real.rpow r α) (Ici 1) := by
  apply (convex_Ici (1 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro r hr
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    exact (Real.hasDerivAt_rpow_const (p := α) (Or.inl hr0.ne')).differentiableAt
  · intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
    simp only [Real.rpow_eq_pow]
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
      (Real.hasDerivAt_rpow_const (p := α) (Or.inl hr0.ne')).deriv,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith))

/-- Clamping the inner radius to one proves regularity across the matched
inner flux interface. -/
theorem scalarRadialFluxFactor_exists_lipschitz {d : ℕ} (hd : 3 ≤ d)
    (n : ℕ) (ζ : ℝ) : ∃ K : ℝ≥0, LipschitzWith K (scalarRadialFluxFactor d n ζ) := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  let B := -cylinderRadialConstant d * scalarAnnulusValue d n ζ (cylinderRadialConstant d) / ε ^ 2
  let A : ℝ → ℝ := fun r => max 1 (ε⁻¹ * r)
  have hA : LipschitzWith ‖ε⁻¹‖₊ A := (real_const_mul_lipschitz ε⁻¹).const_max 1
  have hdR : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpow : LipschitzWith (‖(1 : ℝ) - (d : ℝ)‖₊ * ‖ε⁻¹‖₊)
      (fun r => Real.rpow (A r) (1 - (d : ℝ))) := by
    rw [← lipschitzOnWith_univ]
    exact (negativePower_lipschitzOn (by linarith only [hdR])).comp hA.lipschitzOnWith
      (fun r _ => show 1 ≤ A r from le_max_left _ _)
  refine ⟨‖B‖₊ * (‖(1 : ℝ) - (d : ℝ)‖₊ * ‖ε⁻¹‖₊), ?_⟩
  have heq : scalarRadialFluxFactor d n ζ = fun r => B * Real.rpow (A r) (1 - (d : ℝ)) := by
    funext r
    dsimp only [scalarRadialFluxFactor, A, B, ε]
    rw [div_eq_mul_inv r, mul_comm r]
  rw [heq]
  exact (real_const_mul_lipschitz B).comp hpow

end

end CoarseDeGiorgi.SharpnessExamples
