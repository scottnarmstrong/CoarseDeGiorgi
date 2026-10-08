import CoarseDeGiorgi.Foundations.ChainRule.Basic
import Homogenization.Sobolev.Truncation.Approx

namespace CoarseDeGiorgi.Foundations

open Homogenization
open MeasureTheory Filter Topology
open scoped ENNReal

/-- The positive truncation `(u - c)₊` has weak gradient `1_{u>c} Du` for
`W^{1,1}` functions on a bounded open convex domain. -/
theorem hasWeakGradientOn_max_sub_const_w11
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U 1 u) (hDu : GradMemLpOn U 1 Du)
    (hweak : HasWeakGradientOn U u Du) (c : ℝ) :
    HasWeakGradientOn U (fun x => max (u x - c) 0)
      (fun x i => {y | c < u y}.indicator Du x i) := by
  let μ : Measure (Vec d) := volume.restrict U
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  let f : Vec d → ℝ := fun x => max (u x - c) 0
  let Dpos : Vec d → Vec d := fun x => {y | c < u y}.indicator Du x
  have hfinite : IsFiniteMeasure μ := by
    simpa [μ] using hU.isFiniteMeasure_restrict_volume
  have hp1 : (1 : ℝ≥0∞) ≤ 1 := by norm_num
  have hpTop : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2δlim : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
    have h := hδlim.const_mul (2 : ℝ)
    simpa using h
  have hf_aesm : AEStronglyMeasurable f μ := by
    exact (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      hu.aestronglyMeasurable)
  have hf_mem : MemLp f 1 μ := by
    refine MemLp.of_le (hu.sub (memLp_const c)) hf_aesm ?_
    filter_upwards with x
    simp only [f, Real.norm_eq_abs, Pi.sub_apply]
    rcases le_or_gt (u x - c) 0 with h | h
    · simp only [max_eq_right h, abs_zero]
      positivity
    · rw [max_eq_left h.le]
  have hDpos_coord : ∀ i,
      (fun x => Dpos x i) = {x | c < u x}.indicator (fun x => Du x i) := by
    intro i
    funext x
    by_cases hx : c < u x <;> simp [Dpos, Set.indicator_apply, hx]
  have hDpos_aesm : ∀ i, AEStronglyMeasurable (fun x => Dpos x i) μ := by
    intro i
    have hs : NullMeasurableSet {x | c < u x} μ :=
      nullMeasurableSet_lt (μ := μ) measurable_const.aemeasurable hu.aemeasurable
    rw [hDpos_coord i]
    exact (hDu i).aestronglyMeasurable.indicator₀ hs
  have hDpos_mem : ∀ i, MemLp (fun x => Dpos x i) 1 μ := by
    intro i
    refine MemLp.of_le (hDu i) (hDpos_aesm i) ?_
    filter_upwards with x
    by_cases hx : c < u x <;> simp [Dpos, Set.indicator_apply, hx]
  have hDpos_eq : ∀ x i,
      Dpos x i = (if c < u x then (1 : ℝ) else 0) * Du x i := by
    intro x i
    by_cases hx : c < u x <;> simp [Dpos, Set.indicator_apply, hx]
  set un : ℕ → Vec d → ℝ := fun n x => GApprox c (δ n) (u x) with hun_def
  set gn : Fin d → ℕ → Vec d → ℝ := fun i n x =>
    gStep c (δ n) (u x) * Du x i with hgn_def
  have hun_aesm : ∀ n, AEStronglyMeasurable (un n) μ := by
    intro n
    exact (GApprox_contDiff_one c (δ n)).continuous.comp_aestronglyMeasurable
      hu.aestronglyMeasurable
  have hgn_aesm : ∀ i n, AEStronglyMeasurable
      (fun x => gStep c (δ n) (u x) * Du x i) μ := by
    intro i n
    exact ((gStep_continuous c (δ n)).comp_aestronglyMeasurable
      hu.aestronglyMeasurable).mul (hDu i).aestronglyMeasurable
  have hun_mem : ∀ n, MemLp (un n) 1 μ := by
    intro n
    refine MemLp.of_le (hu.sub (memLp_const c)) (hun_aesm n) ?_
    filter_upwards with x
    rw [hun_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_GApprox_le c (δ n) (u x)
  have hun_ui : UnifIntegrable un 1 μ := by
    apply (unifIntegrable_const hp1 hpTop (hu.sub (memLp_const c))).ae_mono hun_aesm
    intro n
    filter_upwards with x
    rw [hun_def]
    simpa only [Real.enorm_eq_ofReal_abs, Pi.sub_apply] using
      ENNReal.ofReal_le_ofReal (abs_GApprox_le c (δ n) (u x))
  have hf_lim_ae : ∀ x, Tendsto (fun n => un n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2δlim
    rw [Real.norm_eq_abs]
    change |GApprox c (δ n) (u x) - max (u x - c) 0| ≤ 2 * δ n
    exact abs_GApprox_sub_le (hδpos n) (u x)
  have hun_conv : Tendsto
      (fun n => eLpNorm (un n - f) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae hp1 hpTop hun_aesm hf_mem hun_ui
      (Filter.Eventually.of_forall hf_lim_ae)
  have hgn_ui : ∀ i, UnifIntegrable
      (fun n x => gStep c (δ n) (u x) * Du x i) 1 μ := by
    intro i
    apply (unifIntegrable_const hp1 hpTop (hDu i)).ae_mono (hgn_aesm i)
    intro n
    filter_upwards with x
    have hnorm : ‖gStep c (δ n) (u x) * Du x i‖ ≤ ‖Du x i‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gStep_nonneg c (δ n) (u x))]
      calc
        gStep c (δ n) (u x) * |Du x i|
            ≤ 1 * |Du x i| :=
              mul_le_mul_of_nonneg_right (gStep_le_one c (δ n) (u x)) (abs_nonneg _)
        _ = |Du x i| := one_mul _
    simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
      ENNReal.ofReal_le_ofReal hnorm
  have hgn_mem : ∀ i n, MemLp
      (fun x => gStep c (δ n) (u x) * Du x i) 1 μ := by
    intro i n
    refine MemLp.of_le (hDu i) (hgn_aesm i n) ?_
    filter_upwards with x
    have hnorm : ‖gStep c (δ n) (u x) * Du x i‖ ≤ ‖Du x i‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (gStep_nonneg c (δ n) (u x))]
      calc
        gStep c (δ n) (u x) * |Du x i|
            ≤ 1 * |Du x i| :=
              mul_le_mul_of_nonneg_right (gStep_le_one c (δ n) (u x)) (abs_nonneg _)
        _ = |Du x i| := one_mul _
    simpa only [Real.norm_eq_abs] using hnorm
  have hweak_n : ∀ n, HasWeakGradientOn U (un n)
      (fun x j => deriv (GApprox c (δ n)) (u x) * Du x j) := by
    intro n
    exact hasWeakGradientOn_comp_of_deriv_bounded_w11 hU hu hDu hweak
      (GApprox_contDiff_one c (δ n)) (by norm_num) (abs_deriv_GApprox_le c (δ n))
  have hgn_eq : ∀ i n, gn i n = fun x =>
      deriv (GApprox c (δ n)) (u x) * Du x i := by
    intro i n
    funext x
    simp only [hgn_def, deriv_GApprox]
  have hgn_conv : ∀ i, Tendsto
      (fun n => eLpNorm (gn i n - fun x => Dpos x i) 1 μ)
      atTop (𝓝 0) := by
    intro i
    have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => gn i n x) atTop (𝓝 (Dpos x i)) := by
      filter_upwards with x
      have h := (tendsto_gStep (c := c) hδpos hδlim (u x)).mul_const (Du x i)
      simpa only [hgn_def, hDpos_eq x i] using h
    exact tendsto_Lp_finite_of_tendsto_ae hp1 hpTop (hgn_aesm i)
      (hDpos_mem i) (hgn_ui i) (by
        exact hlim)
  have hweak_pos : HasWeakGradientOn U f Dpos := by
    intro i
    have hgn_lim : Tendsto
        (fun n => eLpNorm (gn i n - fun x => Dpos x i) 1 μ)
        atTop (𝓝 0) := hgn_conv i
    exact hasWeakPartialDerivOn_of_tendsto_eLpNorm_one hf_mem (hDpos_mem i)
      (fun n => hun_mem n) (fun n => hgn_mem i n)
      (fun n => by
        have h := hweak_n n i
        simpa only [← hgn_eq i n] using h)
      hun_conv hgn_lim
  simpa [f, Dpos] using hweak_pos

end Foundations
