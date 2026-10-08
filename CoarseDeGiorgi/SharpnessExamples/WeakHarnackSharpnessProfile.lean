module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessMoments
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The smooth radial profile of the weak Harnack supersolutions

In the variable `σ = |x|²`, the flux is `H(σ) x` with `H = P Q`, `P` a smooth cutoff and
`Q(σ) = σ^{-d/2}`. The profile is `U(s) = ∫_s^{d/2} k`, with `k = P Q / (2 a)`.
-/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

/-- The smooth cutoff, zero for `σ ≤ ε²` and one for `σ ≥ 4ε²`. -/
def whP (ε σ : ℝ) : ℝ := Real.smoothTransition ((σ - ε ^ 2) / (3 * ε ^ 2))

/-- `Q(σ) = σ^{-d/2}`. -/
def whQ (d : ℕ) (σ : ℝ) : ℝ := σ ^ (-((d : ℝ) / 2))

/-- The flux factor `H = P Q`. -/
def whH (d : ℕ) (ε σ : ℝ) : ℝ := whP ε σ * whQ d σ

/-- The radial profile in the variable `σ`. -/
def whAs (d : ℕ) (q t σ : ℝ) : ℝ := whA d q t (Real.sqrt σ)

/-- The unit-flux gradient factor. -/
def whK (d : ℕ) (q t σ : ℝ) : ℝ := whQ d σ / (2 * whAs d q t σ)

/-- The gradient factor of the supersolution. -/
def whk (d : ℕ) (q t ε σ : ℝ) : ℝ := whP ε σ * whK d q t σ

/-- The profile of the supersolution. -/
def whU (d : ℕ) (q t ε s : ℝ) : ℝ := ∫ σ in s..((d : ℝ) / 2), whk d q t ε σ

theorem contDiff_whP (ε : ℝ) : ContDiff ℝ ∞ (whP ε) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem whP_nonneg (ε σ : ℝ) : 0 ≤ whP ε σ := Real.smoothTransition.nonneg _

theorem whP_eq_zero {ε σ : ℝ} (h : σ ≤ ε ^ 2) : whP ε σ = 0 := by
  unfold whP
  apply Real.smoothTransition.zero_of_nonpos
  have : 0 ≤ 3 * ε ^ 2 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) this

theorem whP_eq_one {ε σ : ℝ} (hε : 0 < ε) (h : 4 * ε ^ 2 ≤ σ) : whP ε σ = 1 := by
  unfold whP
  apply Real.smoothTransition.one_of_one_le
  have : 0 < 3 * ε ^ 2 := by positivity
  rw [le_div_iff₀ this]
  linarith

theorem whP_monotone {ε : ℝ} (hε : 0 < ε) : Monotone (whP ε) := by
  intro a b hab
  unfold whP
  apply Real.smoothTransition.monotone
  have : 0 < 3 * ε ^ 2 := by positivity
  exact div_le_div_of_nonneg_right (by linarith) this.le

theorem whQ_pos {d : ℕ} {σ : ℝ} (hσ : 0 < σ) : 0 < whQ d σ := Real.rpow_pos_of_pos hσ _

theorem contDiff_whH (d : ℕ) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (whH d ε) := by
  rw [contDiff_iff_contDiffAt]
  intro σ
  by_cases hσ : 0 < σ
  · exact ((contDiff_whP ε).contDiffAt).mul
      (contDiffAt_id.rpow_const_of_ne hσ.ne')
  · have hev : whH d ε =ᶠ[𝓝 σ] fun _ => (0 : ℝ) := by
      have : ∀ᶠ σ' in 𝓝 σ, σ' < ε ^ 2 :=
        (isOpen_Iio.mem_nhds (show σ < ε ^ 2 by nlinarith [not_lt.1 hσ, sq_nonneg ε, pow_pos hε 2]))
      filter_upwards [this] with σ' hσ'
      simp [whH, whP_eq_zero hσ'.le]
    exact (contDiffAt_const).congr_of_eventuallyEq hev

/-- The divergence of the flux `H(|x|²) x` is a nonnegative multiple of `P'`. -/
theorem whH_div_nonneg (d : ℕ) {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    0 ≤ (d : ℝ) * whH d ε σ + 2 * σ * deriv (whH d ε) σ := by
  by_cases hs : σ < ε ^ 2
  · have hev : whH d ε =ᶠ[𝓝 σ] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with σ' hσ'
      simp [whH, whP_eq_zero (le_of_lt hσ')]
    rw [hev.deriv_eq, hev.eq_of_nhds]
    simp
  · have hs' : ε ^ 2 ≤ σ := not_lt.1 hs
    have hσ0 : 0 < σ := lt_of_lt_of_le (pow_pos hε 2) hs'
    have hP : HasDerivAt (whP ε) (deriv (whP ε) σ) σ :=
      (((contDiff_whP ε).differentiable (by simp)) σ).hasDerivAt
    have hQ : HasDerivAt (whQ d) (-((d : ℝ) / 2) * σ ^ (-((d : ℝ) / 2) - 1)) σ :=
      Real.hasDerivAt_rpow_const (Or.inl hσ0.ne')
    have hH := hP.mul hQ
    have hHd : deriv (whH d ε) σ = deriv (whP ε) σ * whQ d σ +
        whP ε σ * (-((d : ℝ) / 2) * σ ^ (-((d : ℝ) / 2) - 1)) := hH.deriv
    have hmon : 0 ≤ deriv (whP ε) σ := hP.nonneg_of_monotone (whP_monotone hε)
    have hQpos := whQ_pos (d := d) hσ0
    have hrel : σ * σ ^ (-((d : ℝ) / 2) - 1) = whQ d σ := by
      rw [Real.rpow_sub_one hσ0.ne']
      unfold whQ
      field_simp
    rw [hHd]
    unfold whH
    have : (d : ℝ) * (whP ε σ * whQ d σ) + 2 * σ * (deriv (whP ε) σ * whQ d σ +
        whP ε σ * (-((d : ℝ) / 2) * σ ^ (-((d : ℝ) / 2) - 1))) =
        2 * σ * deriv (whP ε) σ * whQ d σ := by
      linear_combination (-(d : ℝ) * whP ε σ) * hrel
    rw [this]
    positivity

end

end CoarseDeGiorgi.SharpnessExamples
