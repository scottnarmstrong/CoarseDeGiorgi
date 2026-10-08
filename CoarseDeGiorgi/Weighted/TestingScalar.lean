import CoarseDeGiorgi.Weighted.TestingProducts
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.Support

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped NNReal

/-- Bounded smooth scalar maps fixing zero approximate the identity, with
one uniform derivative bound and pointwise convergence of derivatives. -/
theorem exists_testing_scalar_approximation :
    ∃ (L : ℝ≥0) (Φ : ℕ → ℝ → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (Φ n)) ∧ (∀ n, Φ n 0 = 0) ∧
      (∀ n t, |deriv (Φ n) t| ≤ L) ∧
      (∀ n, ∃ M : ℝ≥0, ∀ t, |Φ n t| ≤ M) ∧
      (∀ n t, |Φ n t| ≤ L * |t|) ∧
      (∀ t, Tendsto (fun n => Φ n t) atTop (𝓝 t)) ∧
      (∀ t, Tendsto (fun n => deriv (Φ n) t) atTop (𝓝 1)) := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let ψ : ℝ → ℝ := fun t => t * b t
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_id.mul b.contDiff
  have hψc : HasCompactSupport ψ := b.hasCompactSupport.mul_left
  obtain ⟨C, hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hψc.comp_left norm_zero)
  obtain ⟨D, hD⟩ := (hψ.continuous_deriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hψc.deriv.comp_left norm_zero)
  let L : ℝ≥0 := ⟨max D 0, le_max_right _ _⟩
  let Φ : ℕ → ℝ → ℝ := fun n t => (n + 1) * ψ (t / (n + 1))
  have hN (n : ℕ) : (n + 1 : ℝ) ≠ 0 := by positivity
  have hΦ (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Φ n) :=
    contDiff_const.mul (hψ.comp (contDiff_id.div_const (n + 1 : ℝ)))
  have hd (n : ℕ) (t : ℝ) : deriv (Φ n) t = deriv ψ (t / (n + 1)) := by
    have h := ((hψ.differentiable (by simp)).differentiableAt.hasDerivAt.comp t
      ((hasDerivAt_id t).div_const (n + 1 : ℝ))).const_mul (n + 1 : ℝ)
    have h' : HasDerivAt (Φ n)
        ((n + 1 : ℝ) * (deriv ψ (t / (n + 1)) * (1 / (n + 1)))) t := by
      simpa only [Φ, Function.comp_def, id_eq] using h
    rw [h'.deriv]
    field_simp
  have hbound (n : ℕ) (t : ℝ) : |deriv (Φ n) t| ≤ L := by
    rw [hd]
    exact (show ‖deriv ψ (t / (n + 1))‖ ≤ D from hD (Set.mem_range_self _)).trans
      (le_max_left _ _)
  have hz (n : ℕ) : Φ n 0 = 0 := by simp only [Φ, ψ, zero_div, zero_mul, mul_zero]
  have hl (n : ℕ) : LipschitzWith L (Φ n) := lipschitzWith_of_nnnorm_deriv_le (C := L)
    ((hΦ n).differentiable (by simp)) (fun t => NNReal.coe_le_coe.mp
      (by simpa only [coe_nnnorm, Real.norm_eq_abs] using hbound n t))
  have hev (t : ℝ) : ∀ᶠ n : ℕ in atTop,
      Φ n t = t ∧ deriv (Φ n) t = 1 := by
    have ht : Tendsto (fun n : ℕ => t / (n + 1)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t
    filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1))]
      with n hn
    have hbn : b =ᶠ[𝓝 (t / (n + 1))] (fun _ => 1) := b.eventuallyEq_one_of_mem_ball hn
    have hψid : ψ =ᶠ[𝓝 (t / (n + 1))] id := by
      filter_upwards [hbn] with s hs
      change s * b s = s
      change b s = 1 at hs
      rw [hs, mul_one]
    constructor
    · change (n + 1) * ψ (t / (n + 1)) = t
      rw [hψid.eq_of_nhds]
      exact mul_div_cancel₀ t (hN n)
    · rw [hd]
      exact (hasDerivAt_id (t / (n + 1))).congr_of_eventuallyEq hψid |>.deriv
  refine ⟨L, Φ, hΦ, hz, hbound, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨⟨(n + 1) * max C 0, mul_nonneg (by positivity) (le_max_right _ _)⟩, ?_⟩
    intro t
    change |(n + 1) * ψ (t / (n + 1))| ≤ _
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < n + 1 by positivity)]
    exact mul_le_mul_of_nonneg_left
      ((show ‖ψ (t / (n + 1))‖ ≤ C from hC (Set.mem_range_self _)).trans (le_max_left _ _))
      (by positivity)
  · intro n t
    simpa only [hz n, sub_zero, Real.norm_eq_abs] using (hl n).norm_sub_le t 0
  · intro t
    exact tendsto_const_nhds.congr' ((hev t).mono fun _ h => h.1.symm)
  · intro t
    exact tendsto_const_nhds.congr' ((hev t).mono fun _ h => h.2.symm)


end CoarseDeGiorgi.Weighted
