import CoarseDeGiorgi.Foundations.ChainRule.PositivePart

namespace CoarseDeGiorgi.Foundations

open Homogenization
open MeasureTheory Filter Topology
open scoped ENNReal

private theorem hasWeakPartialDerivOn_sub_w11
    {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u v gu gv : Vec d → ℝ}
    (hu : MemLpOn U 1 u) (hv : MemLpOn U 1 v)
    (hgu : MemLpOn U 1 gu) (hgv : MemLpOn U 1 gv)
    (hweak_u : HasWeakPartialDerivOn U i u gu)
    (hweak_v : HasWeakPartialDerivOn U i v gv) :
    HasWeakPartialDerivOn U i (fun x => u x - v x) (fun x => gu x - gv x) := by
  let μ : Measure (Vec d) := volume.restrict U
  let _ : ENNReal.HolderConjugate (1 : ℝ≥0∞) ⊤ := ENNReal.HolderConjugate.one_top
  intro φ hφ hφc hφs
  have hDφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) ⊤ μ := by
    have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      apply HasCompactSupport.mono' (hφc.fderiv ℝ)
      intro x hx
      apply subset_tsupport (fderiv ℝ φ)
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]
      simp
    exact hcont.memLp_top_of_hasCompactSupport hcs μ
  have hφmem : MemLp φ ⊤ μ := hφ.continuous.memLp_top_of_hasCompactSupport hφc μ
  have huD : Integrable (fun x => u x * (fderiv ℝ φ x) (basisVec i)) μ := by
    simpa [μ, mul_comm] using
      (memLp_one_iff_integrable.mp (hDφ.fun_mul hu))
  have hvD : Integrable (fun x => v x * (fderiv ℝ φ x) (basisVec i)) μ := by
    simpa [μ, mul_comm] using
      (memLp_one_iff_integrable.mp (hDφ.fun_mul hv))
  have hguφ : Integrable (fun x => gu x * φ x) μ := by
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hφmem.fun_mul hgu))
  have hgvφ : Integrable (fun x => gv x * φ x) μ := by
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hφmem.fun_mul hgv))
  have hleft :
      (∫ x in U, (u x - v x) * (fderiv ℝ φ x) (basisVec i) ∂volume) =
        (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume) -
          (∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂volume) := by
    rw [← integral_sub huD hvD]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  have hright :
      (∫ x in U, (gu x - gv x) * φ x ∂volume) =
        (∫ x in U, gu x * φ x ∂volume) - (∫ x in U, gv x * φ x ∂volume) := by
    rw [← integral_sub hguφ hgvφ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [hleft, hright, hweak_u φ hφ hφc hφs, hweak_v φ hφ hφc hφs]
  ring

/-- The weak gradient vanishes on a level set for `W^{1,1}` functions on a
bounded open convex domain. -/
theorem grad_ae_zero_on_level_set_w11
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U 1 u) (hDu : GradMemLpOn U 1 Du)
    (hweak : HasWeakGradientOn U u Du) (c : ℝ) :
    (fun x => {y | u y = c}.indicator Du x) =ᵐ[volume.restrict U] (fun _ => 0) := by
  let μ : Measure (Vec d) := volume.restrict U
  let P : Vec d → ℝ := fun x => max (u x - c) 0
  let Q : Vec d → ℝ := fun x => max (-u x - -c) 0
  let DP : Vec d → Vec d := fun x => {y | c < u y}.indicator Du x
  let DQ : Vec d → Vec d := fun x => {y | -c < -u y}.indicator (fun x => -Du x) x
  have hfinite : IsFiniteMeasure μ := by
    simpa [μ] using hU.isFiniteMeasure_restrict_volume
  have hP : HasWeakGradientOn U P DP := by
    simpa [P, DP] using hasWeakGradientOn_max_sub_const_w11 hU hu hDu hweak c
  have hNegWeak : HasWeakGradientOn U (fun x => -u x) (fun x i => -Du x i) := by
    have h := hasWeakGradientOn_comp_of_deriv_bounded_w11 hU hu hDu hweak
      (Φ := fun t : ℝ => -t) (contDiff_id.neg) (M := 1) (by norm_num)
      (by intro t; simp)
    simpa only [deriv_neg'', neg_one_mul, Pi.neg_apply] using h
  have hNegMem : MemLpOn U 1 (fun x => -u x) := by
    change MemLp (fun x => -u x) 1 μ
    convert hu.neg using 1
  have hNegDuMem : GradMemLpOn U 1 (fun x => -Du x) := by
    intro i
    change MemLp (fun x => -Du x i) 1 μ
    convert (hDu i).neg using 1
  have hQ : HasWeakGradientOn U Q DQ := by
    simpa [Q, DQ] using hasWeakGradientOn_max_sub_const_w11
      hU hNegMem hNegDuMem hNegWeak (-c)
  have hshift : HasWeakGradientOn U (fun x => u x - c) Du := by
    have h := hasWeakGradientOn_comp_of_deriv_bounded_w11 hU hu hDu hweak
      (Φ := fun t : ℝ => t - c) (contDiff_id.sub contDiff_const) (M := 1)
      (by norm_num) (by intro t; simp)
    simpa using h
  have hPmem : MemLp P 1 μ := by
    refine MemLp.of_le (hu.sub (memLp_const c)) ?_ ?_
    · exact (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
        hu.aestronglyMeasurable)
    · filter_upwards with x
      simp only [P, Real.norm_eq_abs, Pi.sub_apply]
      rcases le_or_gt (u x - c) 0 with h | h
      · simp only [max_eq_right h, abs_zero]
        positivity
      · rw [max_eq_left h.le]
  have hQmem : MemLp Q 1 μ := by
    refine MemLp.of_le (hNegMem.sub (memLp_const (-c))) ?_ ?_
    · exact (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
        hNegMem.aestronglyMeasurable)
    · filter_upwards with x
      simp only [Q, Real.norm_eq_abs, Pi.sub_apply]
      rcases le_or_gt (-u x - -c) 0 with h | h
      · simp only [max_eq_right h, abs_zero]
        positivity
      · rw [max_eq_left h.le]
  have hDP_coord : ∀ i,
      (fun x => DP x i) = {x | c < u x}.indicator (fun x => Du x i) := by
    intro i
    funext x
    by_cases hx : c < u x <;> simp [DP, Set.indicator_apply, hx]
  have hDQ_coord : ∀ i,
      (fun x => DQ x i) = {x | -c < -u x}.indicator (fun x => -Du x i) := by
    intro i
    funext x
    simp only [DQ, Set.indicator_apply, Set.mem_ofPred_eq, ite_apply,
      Pi.neg_apply, Pi.zero_apply]
  have hDPmem : ∀ i, MemLp (fun x => DP x i) 1 μ := by
    intro i
    have hs : NullMeasurableSet {x | c < u x} μ :=
      nullMeasurableSet_lt (μ := μ) measurable_const.aemeasurable hu.aemeasurable
    rw [hDP_coord i]
    refine MemLp.of_le (hDu i) ((hDu i).aestronglyMeasurable.indicator₀ hs) ?_
    filter_upwards with x
    by_cases hx : c < u x <;> simp [hx]
  have hDQmem : ∀ i, MemLp (fun x => DQ x i) 1 μ := by
    intro i
    have hs : NullMeasurableSet {x | -c < -u x} μ :=
      nullMeasurableSet_lt (μ := μ) measurable_const.aemeasurable
        ((hNegMem).aemeasurable)
    rw [hDQ_coord i]
    refine MemLp.of_le (hNegDuMem i)
      ((hNegDuMem i).aestronglyMeasurable.indicator₀ hs) ?_
    filter_upwards with x
    by_cases hx : u x < c <;> simp [hx]
  have hweak_sub : HasWeakGradientOn U (fun x => P x - Q x)
      (fun x => DP x - DQ x) := by
    intro i
    exact hasWeakPartialDerivOn_sub_w11 hPmem hQmem (hDPmem i) (hDQmem i)
      (hP i) (hQ i)
  have hvalue : (fun x => P x - Q x) = (fun x => u x - c) := by
    funext x
    dsimp [P, Q]
    have hQ' : max (-u x - -c) 0 = max (c - u x) 0 := by
      congr 1
      ring
    rw [hQ']
    rcases le_total (u x - c) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  rw [hvalue] at hweak_sub
  have hDPsubmem : ∀ i, MemLp (fun x => DP x i - DQ x i) 1 μ := by
    intro i
    exact (hDPmem i).sub (hDQmem i)
  have hloc (g : Vec d → ℝ) (hg : MemLp g 1 μ) :
      LocallyIntegrableOn g U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num))
  have hcoord : ∀ i, (fun x => DP x i - DQ x i) =ᵐ[μ] (fun x => Du x i) := by
    intro i
    exact HasWeakPartialDerivOn.ae_eq hU.isOpen (hloc _ (hDPsubmem i)) (hloc _ (hDu i))
      (hweak_sub i) (hshift i)
  have hall : ∀ᵐ x ∂μ, ∀ i, DP x i - DQ x i = Du x i := ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx
  by_cases hlevel : u x = c
  · have hDPzero : DP x = 0 := by
      funext i
      simp [DP, Set.indicator_apply, hlevel]
    have hDQzero : DQ x = 0 := by
      funext i
      simp [DQ, Set.indicator_apply, hlevel]
    have hDuZero : Du x = 0 := by
      funext i
      have hi := hx i
      rw [hDPzero, hDQzero] at hi
      simpa using hi.symm
    simp [hlevel, hDuZero]
  · simp [hlevel]

end Foundations
