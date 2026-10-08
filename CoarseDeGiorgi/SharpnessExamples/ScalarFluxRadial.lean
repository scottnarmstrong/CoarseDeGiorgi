module

public import CoarseDeGiorgi.SharpnessExamples.ScalarGradient

/-! # A continuous matched radial flux and an outer monotone cutoff -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open CoarseDeGiorgi.Sharpness
open scoped NNReal

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The matched transverse flux divided by the transverse coordinate. -/
def scalarRadialFluxFactor (d n : ℕ) (ζ r : ℝ) : ℝ :=
  let κ := cylinderRadialConstant d
  let ε := cylinderRadius d n ζ κ;
  -κ * scalarAnnulusValue d n ζ κ / ε ^ 2 * Real.rpow (max 1 (r / ε)) (1 - (d : ℝ))

/-- A nonincreasing cutoff supported in the closed outer cylinder. -/
def scalarOuterFluxCutoff (ε δ r : ℝ) : ℝ := min (max ((2 * ε - r) / δ) 0) 1

theorem scalarOuterFluxCutoff_bounds (ε δ r : ℝ) :
    0 ≤ scalarOuterFluxCutoff ε δ r ∧ scalarOuterFluxCutoff ε δ r ≤ 1 :=
  ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

theorem scalarOuterFluxCutoff_eq_one {ε δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ 2 * ε - δ) :
    scalarOuterFluxCutoff ε δ r = 1 := by
  have h : 1 ≤ (2 * ε - r) / δ := (le_div_iff₀ hδ).2 (by linarith)
  simp only [scalarOuterFluxCutoff, max_eq_left (zero_le_one.trans h), min_eq_right h]

theorem scalarOuterFluxCutoff_eq_zero {ε δ r : ℝ} (hδ : 0 < δ) (hr : 2 * ε ≤ r) :
    scalarOuterFluxCutoff ε δ r = 0 := by
  have h : (2 * ε - r) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hδ.le
  simp only [scalarOuterFluxCutoff, max_eq_right h, min_eq_left (by norm_num : (0 : ℝ) ≤ 1)]

theorem scalarOuterFluxCutoff_hasDerivAt {ε δ r : ℝ} (hδ : 0 < δ)
    (hleft : r ≠ 2 * ε - δ) (hright : r ≠ 2 * ε) :
    HasDerivAt (scalarOuterFluxCutoff ε δ)
      (if 2 * ε - δ < r ∧ r < 2 * ε then -δ⁻¹ else 0) r := by
  by_cases h1 : r < 2 * ε - δ
  · have heq : scalarOuterFluxCutoff ε δ =ᶠ[𝓝 r] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_lt_nhds h1] with t ht
      exact scalarOuterFluxCutoff_eq_one hδ ht.le
    rw [ite_eq_right (fun h => (not_lt.mpr h1.le) h.1)]
    exact (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq heq
  · have h1' : 2 * ε - δ < r := lt_of_le_of_ne (le_of_not_gt h1) hleft.symm
    by_cases h2 : r < 2 * ε
    · have heq : scalarOuterFluxCutoff ε δ =ᶠ[𝓝 r] fun t => (2 * ε - t) / δ := by
        filter_upwards [Ioo_mem_nhds h1' h2] with t ht
        have hpos : 0 ≤ (2 * ε - t) / δ := div_nonneg (by linarith only [ht.2]) hδ.le
        have hle : (2 * ε - t) / δ ≤ 1 := (div_le_one hδ).2 (by linarith only [ht.1])
        simp only [scalarOuterFluxCutoff, max_eq_left hpos, min_eq_left hle]
      rw [ite_eq_left ⟨h1', h2⟩]
      convert (((hasDerivAt_const r (2 * ε)).sub (hasDerivAt_id r)).div_const δ).congr_of_eventuallyEq heq using 1
      simp only [zero_sub, div_eq_mul_inv, neg_mul, one_mul]
    · have h2' : 2 * ε < r := lt_of_le_of_ne (le_of_not_gt h2) hright.symm
      have heq : scalarOuterFluxCutoff ε δ =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
        filter_upwards [eventually_gt_nhds h2'] with t ht
        exact scalarOuterFluxCutoff_eq_zero hδ ht.le
      rw [ite_eq_right (fun h => h2 h.2)]
      exact (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq heq

theorem scalarOuterFluxCutoff_exists_lipschitz (ε δ : ℝ) :
    ∃ K : ℝ≥0, LipschitzWith K (scalarOuterFluxCutoff ε δ) := by
  have hscale : LipschitzWith ‖δ⁻¹‖₊ (fun r : ℝ => (2 * ε - r) / δ) := by
    apply LipschitzWith.of_dist_le_mul
    intro r t
    simp only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
    rw [← sub_div, abs_div, abs_inv]
    have h : 2 * ε - r - (2 * ε - t) = -(r - t) := by ring
    rw [h, abs_neg, div_eq_mul_inv, mul_comm]
  exact ⟨‖δ⁻¹‖₊, (hscale.max_const 0).min_const 1⟩

theorem scalarRadialFluxFactor_core {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hr : r ≤ cylinderRadius d n ζ (cylinderRadialConstant d)) :
    scalarRadialFluxFactor d n ζ r =
      scalarCoreValue d n ζ (cylinderRadialConstant d) *
        (-2 * scalarProfileXi d n ζ / (cylinderRadius d n ζ (cylinderRadialConstant d)) ^ 2) := by
  let ε := cylinderRadius d n ζ (cylinderRadialConstant d)
  have hε := (cylinderRadius_data (d := d) (n := n) hd hζ0 hζ2 (cylinderRadialConstant_pos hd)).1
  have hratio : r / ε ≤ 1 := (div_le_one hε).2 hr
  have hmatch := scalarProfile_inner_flux_match (n := n) hd hζ0 hζ2
  have hdiv := congrArg (fun t : ℝ => t / ε) hmatch
  dsimp only [scalarRadialFluxFactor]
  rw [max_eq_left hratio, Real.rpow_eq_pow, Real.one_rpow, mul_one]
  change -cylinderRadialConstant d * scalarAnnulusValue d n ζ (cylinderRadialConstant d) / ε ^ 2 = _
  convert hdiv.symm using 1 <;> dsimp only [ε] <;> field_simp [hε.ne']

theorem scalarRadialFluxFactor_hasDerivAt_core {d : ℕ} (hd : 3 ≤ d) {n : ℕ} {ζ r : ℝ}
    (hζ0 : 0 < ζ) (hζ2 : ζ < 2)
    (hr : r < cylinderRadius d n ζ (cylinderRadialConstant d)) :
    HasDerivAt (scalarRadialFluxFactor d n ζ) 0 r := by
  have heq : scalarRadialFluxFactor d n ζ =ᶠ[𝓝 r] fun _ =>
      scalarCoreValue d n ζ (cylinderRadialConstant d) *
        (-2 * scalarProfileXi d n ζ / (cylinderRadius d n ζ (cylinderRadialConstant d)) ^ 2) := by
    filter_upwards [eventually_lt_nhds hr] with t ht
    exact scalarRadialFluxFactor_core hd hζ0 hζ2 ht.le
  exact (hasDerivAt_const r _).congr_of_eventuallyEq heq

end

end CoarseDeGiorgi.SharpnessExamples
