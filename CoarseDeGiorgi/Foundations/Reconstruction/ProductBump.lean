module

public import CoarseDeGiorgi.Foundations.Reconstruction.Defs
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Pi

/-! # A nonnegative smooth probability bump with sup-norm cube support -/

@[expose] public section

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- Fixed one-dimensional bump, independent of all problem parameters. -/
def reconstructionBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The normalized one-dimensional probability density built from `reconstructionBump`. -/
def reconstructionEta : ℝ → ℝ := reconstructionBump.normed volume

theorem reconstructionEta_nonneg (x : ℝ) : 0 ≤ reconstructionEta x :=
  reconstructionBump.nonneg_normed x

theorem contDiff_reconstructionEta : ContDiff ℝ (⊤ : ℕ∞) reconstructionEta :=
  reconstructionBump.contDiff_normed

theorem integrable_reconstructionEta : Integrable reconstructionEta volume :=
  reconstructionBump.integrable_normed

theorem integral_reconstructionEta : ∫ x, reconstructionEta x ∂volume = 1 :=
  reconstructionBump.integral_normed

theorem reconstructionEta_ne_zero_iff (x : ℝ) : reconstructionEta x ≠ 0 ↔ |x| < 1 / 2 := by
  have h := reconstructionBump.support_normed_eq (μ := volume)
  have hx := Set.ext_iff.mp h x
  simpa only [Function.mem_support, reconstructionEta, Metric.mem_ball, dist_zero_right,
    Real.norm_eq_abs, reconstructionBump] using hx

/-- Tensor product bump on the sup-norm ambient carrier. -/
def reconstructionRho {d : ℕ} (x : Vec d) : ℝ := ∏ i : Fin d, reconstructionEta (x i)

variable {d : ℕ}

theorem reconstructionRho_nonneg (x : Vec d) : 0 ≤ reconstructionRho x :=
  Finset.prod_nonneg fun i _ => reconstructionEta_nonneg (x i)

theorem contDiff_reconstructionRho : ContDiff ℝ (⊤ : ℕ∞) (reconstructionRho (d := d)) :=
  contDiff_prod fun i _ => contDiff_reconstructionEta.comp (contDiff_apply ℝ ℝ i)

theorem integrable_reconstructionRho : Integrable (reconstructionRho (d := d)) volume :=
  Integrable.fintype_prod fun _ => integrable_reconstructionEta

theorem integral_reconstructionRho : ∫ x : Vec d, reconstructionRho x ∂volume = 1 := by
  unfold reconstructionRho
  rw [integral_fintype_prod_volume_eq_pow, integral_reconstructionEta, one_pow]

theorem support_reconstructionRho_subset :
    Function.support (reconstructionRho (d := d)) ⊆ Metric.closedBall 0 (1 / 2 : ℝ) := by
  classical
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro i
  have hi : reconstructionEta (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  exact ((reconstructionEta_ne_zero_iff (x i)).mp hi).le

theorem hasCompactSupport_reconstructionRho : HasCompactSupport (reconstructionRho (d := d)) := by
  apply (isCompact_closedBall (0 : Vec d) (1 / 2 : ℝ)).of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal support_reconstructionRho_subset Metric.isClosed_closedBall

/-- A uniform bound on the bump and its first derivative follows from compact smooth support. -/
theorem exists_bound_reconstructionRho : ∃ A : ℝ, 1 ≤ A ∧
    (∀ x : Vec d, ‖reconstructionRho x‖ ≤ A) ∧
    (∀ x : Vec d, ‖fderiv ℝ reconstructionRho x‖ ≤ A) := by
  obtain ⟨B, hB⟩ := hasCompactSupport_reconstructionRho.exists_bound_of_continuous
    contDiff_reconstructionRho.continuous
  obtain ⟨D, hD⟩ := (hasCompactSupport_reconstructionRho (d := d)).fderiv (𝕜 := ℝ) |>.exists_bound_of_continuous
    (contDiff_reconstructionRho.continuous_fderiv (by norm_num))
  refine ⟨max 1 (max B D), le_max_left _ _, ?_, ?_⟩
  · intro x
    exact (hB x).trans ((le_max_left B D).trans (le_max_right _ _))
  · intro x
    exact (hD x).trans ((le_max_right B D).trans (le_max_right _ _))

end

end CoarseDeGiorgi.Foundations.Reconstruction
