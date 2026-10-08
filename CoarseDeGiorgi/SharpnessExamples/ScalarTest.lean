module

public import CoarseDeGiorgi.SharpnessExamples.ScalarMembership
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Normed.Group.Bounded

/-! # Integration by parts for Lipschitz flux coordinates on the test domain -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped NNReal

namespace CoarseDeGiorgi.SharpnessExamples

/-- A smooth compactly supported scalar test is globally Lipschitz. -/
theorem smoothTest_exists_lipschitz {d : ℕ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ K : ℝ≥0, LipschitzWith K φ := by
  obtain ⟨C, hC⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hc.fderiv ℝ)
  refine ⟨Real.toNNReal (max C 0), lipschitzWith_of_nnnorm_fderiv_le
    (hφ.differentiable (by simp)) ?_⟩
  intro x
  apply NNReal.coe_le_coe.mp
  rw [coe_nnnorm, Real.coe_toNNReal _ (le_max_right _ _)]
  exact (hC x).trans (le_max_left _ _)

/-- Integration by parts remains valid for a flux coordinate that is only
Lipschitz on the open test domain. A real Lipschitz extension supplies the
whole-space identity, and local equality identifies its line derivative. -/
theorem integral_test_mul_lipschitzOn_flux {d : ℕ} {V : Set (Vec d)} (hV : IsOpen V)
    {φ F : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ V) {K : ℝ≥0} (hF : LipschitzOnWith K F V) (v : Vec d) :
    Integrable (fun x => fderiv ℝ φ x v * F x) volume ∧
    Integrable (fun x => φ x * lineDeriv ℝ F x v) volume ∧
    (∫ x, fderiv ℝ φ x v * F x ∂volume) =
      -(∫ x, φ x * lineDeriv ℝ F x v ∂volume) := by
  obtain ⟨E, hE, heq⟩ := hF.extend_real
  obtain ⟨L, hL⟩ := smoothTest_exists_lipschitz hφ hc
  have hderivCont : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hleft : Integrable (fun x => fderiv ℝ φ x v * E x) volume :=
    (hderivCont.mul hE.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ v).mul_right)
  have hright : Integrable (fun x => φ x * lineDeriv ℝ E x v) volume := by
    simpa only [smul_eq_mul] using
      (hE.locallyIntegrable_lineDeriv (μ := volume) v).integrable_smul_left_of_hasCompactSupport
        hφ.continuous hc
  have hleftEq : (fun x => fderiv ℝ φ x v * E x) =
      fun x => fderiv ℝ φ x v * F x := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [← heq (hs hx)]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp only [zero_apply, zero_mul]
  have hrightEq : (fun x => φ x * lineDeriv ℝ E x v) =
      fun x => φ x * lineDeriv ℝ F x v := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · have he : E =ᶠ[𝓝 x] F := by
        filter_upwards [hV.mem_nhds (hs hx)] with y hy
        exact (heq hy).symm
      rw [he.lineDeriv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp only [zero_mul]
  have hibp := hE.integral_lineDeriv_mul_eq (μ := volume) hL hc v
  have htest : (fun x => lineDeriv ℝ φ x (-v) * E x) =
      fun x => -(fderiv ℝ φ x v * E x) := by
    funext x
    rw [lineDeriv_neg, (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    ring
  rw [htest, integral_neg] at hibp
  have hmul : (fun x => lineDeriv ℝ E x v * φ x) =
      fun x => φ x * lineDeriv ℝ E x v := by
    funext x
    exact mul_comm _ _
  rw [hmul] at hibp
  rw [hleftEq] at hleft
  rw [hrightEq] at hright
  refine ⟨hleft, hright, ?_⟩
  rw [hleftEq, hrightEq] at hibp
  linarith only [hibp]

end CoarseDeGiorgi.SharpnessExamples
