module

public import CoarseDeGiorgi.SharpnessExamples.WeakHarnackSharpnessProfile

/-! # Smoothness and monotonicity of the supersolution profile `U` -/

@[expose] public section

open Homogenization MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal ContDiff

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

theorem contDiffAt_whA (d : ℕ) (q t : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffAt ℝ ∞ (whA d q t) ρ := by
  unfold whA whLog
  exact (contDiffAt_id.rpow_const_of_ne hρ.ne').mul
    (((contDiffAt_const.add contDiffAt_const).sub (Real.contDiffAt_log.2 hρ.ne')).pow 3)

theorem contDiffAt_whAs (d : ℕ) (q t : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ContDiffAt ℝ ∞ (whAs d q t) σ :=
  (contDiffAt_whA d q t (Real.sqrt_pos.2 hσ)).comp σ (Real.contDiffAt_sqrt hσ.ne')

theorem whAs_pos {d : ℕ} {q t : ℝ} {σ : ℝ} (hσ : 0 < σ) (hσd : σ ≤ d) :
    0 < whAs d q t σ := by
  unfold whAs
  refine whA_pos (Real.sqrt_pos.2 hσ) ?_
  unfold whR
  exact Real.sqrt_le_sqrt hσd

theorem whk_eq_zero {d : ℕ} (q t : ℝ) {ε σ : ℝ} (h : σ ≤ ε ^ 2) : whk d q t ε σ = 0 := by
  simp [whk, whP_eq_zero h]

theorem whk_nonneg {d : ℕ} (q t : ℝ) {ε σ : ℝ} (hσ : σ ≤ d) :
    0 ≤ whk d q t ε σ := by
  by_cases hσ0 : 0 < σ
  · unfold whk whK
    exact mul_nonneg (whP_nonneg _ _)
      (div_nonneg (whQ_pos hσ0).le (by have := whAs_pos (d := d) (q := q) (t := t) hσ0 hσ; linarith))
  · have : σ ≤ ε ^ 2 := by nlinarith [not_lt.1 hσ0, sq_nonneg ε]
    rw [whk_eq_zero q t this]

theorem contDiffOn_whk {d : ℕ} (q t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (whk d q t ε) (Iio (d : ℝ)) := by
  intro σ hσ
  apply ContDiffAt.contDiffWithinAt
  by_cases hs : σ < ε ^ 2
  · have hev : whk d q t ε =ᶠ[𝓝 σ] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hs] with σ' hσ'
      exact whk_eq_zero q t hσ'.le
    exact (contDiffAt_const).congr_of_eventuallyEq hev
  · have hσ0 : 0 < σ := lt_of_lt_of_le (pow_pos hε 2) (not_lt.1 hs)
    have hAs := whAs_pos (d := d) (q := q) (t := t) hσ0 (le_of_lt hσ)
    unfold whk whK whQ
    refine ((contDiff_whP ε).contDiffAt).mul (ContDiffAt.div ?_ ?_ ?_)
    · exact contDiffAt_id.rpow_const_of_ne hσ0.ne'
    · exact contDiffAt_const.mul (contDiffAt_whAs d q t hσ0)
    · positivity

theorem whk_intervalIntegrable {d : ℕ} (q t : ℝ) {ε : ℝ} (hε : 0 < ε) {a b : ℝ}
    (ha : a < d) (hb : b < d) : IntervalIntegrable (whk d q t ε) volume a b := by
  apply ContinuousOn.intervalIntegrable
  have := (contDiffOn_whk (d := d) q t hε).continuousOn
  refine this.mono ?_
  intro x hx
  rw [uIcc] at hx
  exact lt_of_le_of_lt hx.2 (max_lt ha hb)

theorem hasDerivAt_whU {d : ℕ} (hd : 1 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε) {s : ℝ}
    (hs : s < d) : HasDerivAt (whU d q t ε) (-whk d q t ε s) s := by
  have hhalf : (d : ℝ) / 2 < d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have hcont : ContinuousAt (whk d q t ε) s :=
    ((contDiffOn_whk (d := d) q t hε).continuousOn.continuousAt (isOpen_Iio.mem_nhds hs))
  have hmeas : StronglyMeasurableAtFilter (whk d q t ε) (𝓝 s) volume :=
    (contDiffOn_whk (d := d) q t hε).continuousOn.stronglyMeasurableAtFilter isOpen_Iio s hs
  exact intervalIntegral.integral_hasDerivAt_left (whk_intervalIntegrable q t hε hs hhalf)
    hmeas hcont

theorem contDiffOn_whU {d : ℕ} (hd : 1 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (whU d q t ε) (Iio (d : ℝ)) := by
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Iio]
  refine ⟨fun s hs => (hasDerivAt_whU hd q t hε hs).differentiableAt.differentiableWithinAt, ?_⟩
  exact (contDiffOn_whk (d := d) q t hε).neg.congr (fun s hs => (hasDerivAt_whU hd q t hε hs).deriv)

theorem whU_antitone {d : ℕ} (hd : 1 ≤ d) (q t : ℝ) {ε : ℝ} (hε : 0 < ε) {s s' : ℝ}
    (hss : s ≤ s') (hs' : s' ≤ (d : ℝ) / 2) : whU d q t ε s' ≤ whU d q t ε s := by
  have hhalf : (d : ℝ) / 2 < d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have hsd : s < d := by linarith
  have hs'd : s' < d := by linarith
  have h := intervalIntegral.integral_add_adjacent_intervals
    (whk_intervalIntegrable q t hε hsd hs'd) (whk_intervalIntegrable q t hε hs'd hhalf)
  have hnn : 0 ≤ ∫ σ in s..s', whk d q t ε σ :=
    intervalIntegral.integral_nonneg hss (fun u hu => whk_nonneg q t (by linarith [hu.2]))
  unfold whU
  linarith

end

end CoarseDeGiorgi.SharpnessExamples
