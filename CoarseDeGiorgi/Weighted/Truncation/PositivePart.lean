import CoarseDeGiorgi.Weighted.Truncation.Chain

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The one-sided scalar approximants are infinitely smooth. -/
theorem GApprox_contDiff_top (c δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (GApprox c δ) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun t => (GApprox_hasDerivAt c δ t).differentiableAt,
    by rw [deriv_GApprox]; exact gStep_contDiff c δ⟩

/-- Levels of the positive part belong to the weighted completion. -/
theorem MemH1a.max_sub_const (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) (c : ℝ) :
    CoarseDeGiorgi.MemH1a a V (fun x => max (u x - c) 0)
      ({x | c < u x}.indicator G) := by
  let μ := volume.restrict V
  let : IsFiniteMeasure μ := hV.isFiniteMeasure_restrict_volume
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδpos : ∀ n, 0 < δ n := by intro n; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hi := (memH1a_memW11 hV hne ha hu).1
  have hEG := MemH1a.energy_lt_top hV.isOpen ha hu
  have hs : NullMeasurableSet {x | c < u x} μ :=
    nullMeasurableSet_lt measurable_const.aemeasurable hu.1.aemeasurable
  let χ : Vec d → ℝ := fun x => if c < u x then 1 else 0
  have hχ : AEStronglyMeasurable χ μ := by
    exact aestronglyMeasurable_const.indicator₀ hs
  have hGpos : AEStronglyMeasurable ({x | c < u x}.indicator G) μ :=
    hu.2.1.indicator₀ hs
  have hχG : (fun x => χ x • G x) = {x | c < u x}.indicator G := by
    funext x
    by_cases hx : c < u x <;> simp [χ, hx]
  have hl : LipschitzWith 1 (fun t : ℝ => max (t - c) 0) :=
    (show LipschitzWith 1 (fun t : ℝ => t - c) from by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [sub_sub_sub_cancel_right]).max_const 0
  have hposI := integrableOn_lipschitz_comp hV hi hl
  have hn : ∀ n, CoarseDeGiorgi.MemH1a a V (fun x => GApprox c (δ n) (u x))
      (fun x => gStep c (δ n) (u x) • G x) := by
    intro n
    simpa only [Function.comp_def, deriv_GApprox] using
      MemH1a.comp hV hne ha hu (GApprox_contDiff_top c (δ n))
        (L := 1) (abs_deriv_GApprox_le c (δ n))
  have hvalM (n : ℕ) : AEStronglyMeasurable (fun x => GApprox c (δ n) (u x)) μ :=
    (GApprox_contDiff_one c (δ n)).continuous.comp_aestronglyMeasurable hu.1
  have hbase : MemLp (fun x => u x - c) 1 μ :=
    memLp_one_iff_integrable.mpr (hi.sub (integrable_const c))
  have hui : UnifIntegrable (fun n x => GApprox c (δ n) (u x)) 1 μ := by
    apply (unifIntegrable_const (by norm_num) (by norm_num) hbase).ae_mono hvalM
    intro n
    filter_upwards with x
    simpa only [Real.enorm_eq_ofReal_abs] using
      ENNReal.ofReal_le_ofReal (abs_GApprox_le c (δ n) (u x))
  have hval : Tendsto (fun n => eLpNorm
      ((fun x => GApprox c (δ n) (u x)) - fun x => max (u x - c) 0) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hvalM
      (memLp_one_iff_integrable.mpr hposI) hui
    filter_upwards with x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa using hδ.const_mul (2 : ℝ))
    simpa only [Real.norm_eq_abs, Function.comp_apply] using abs_GApprox_sub_le (hδpos n) (u x)
  have henergy : Tendsto (fun n => weightedEnergy a V
      ((fun x => gStep c (δ n) (u x) • G x) - {x | c < u x}.indicator G)) atTop (𝓝 0) := by
    have ht := tendsto_energy_mul_zero ha hu.2.1 hEG
      (b := fun n x => gStep c (δ n) (u x) - χ x)
      (fun n => ((gStep_continuous c (δ n)).comp_aestronglyMeasurable hu.1).sub hχ)
      (M := 2) (fun n => ?_) ?_
    · convert ht using 1
      funext n
      congr 1
      rw [← hχG]
      funext x
      exact (sub_smul _ _ _).symm
    · filter_upwards with x
      have h1 := gStep_nonneg c (δ n) (u x)
      have h2 := gStep_le_one c (δ n) (u x)
      dsimp [χ]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [h1, h2]
    · filter_upwards with x
      simpa [χ] using (tendsto_gStep (c := c) hδpos hδ (u x)).sub_const (χ x)
  exact memH1a_of_tendsto hV hne ha hn hposI hGpos hval henergy

/-- The exact positive-part gradient display `e.weighted.truncation.gradients`. -/
theorem MemH1a.posPart (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) :
    CoarseDeGiorgi.MemH1a a V (fun x => max (u x) 0) ({x | 0 < u x}.indicator G) := by
  simpa only [sub_zero] using MemH1a.max_sub_const hV hne ha hu 0

omit [NeZero d] in
/-- Positive parts at any level do not increase energy. -/
theorem energy_positivePart_le (ha : IsWeightedCoeffOn V a) (u : Vec d → ℝ)
    (G : Vec d → Vec d) (c : ℝ) :
    weightedEnergy a V ({x | c < u x}.indicator G) ≤ weightedEnergy a V G := by
  have hh := energy_mul_le ha (G := G) (b := fun x => if c < u x then 1 else 0)
    (M := 1) (Eventually.of_forall fun x => by split_ifs <;> norm_num)
  have heq : (fun x => (if c < u x then (1 : ℝ) else 0) • G x) =
      {x | c < u x}.indicator G := by
    funext x
    by_cases hx : c < u x <;> simp [hx]
  rw [heq] at hh
  simpa only [one_pow, ENNReal.ofReal_one, one_mul] using hh

end CoarseDeGiorgi.Weighted
