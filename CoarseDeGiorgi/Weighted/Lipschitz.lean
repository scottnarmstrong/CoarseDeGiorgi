import CoarseDeGiorgi.Foundations.ChainRule.Basic
import CoarseDeGiorgi.Weighted.Truncation.Closure
import CoarseDeGiorgi.Weighted.ZeroCore
import CoarseDeGiorgi.Foundations.Euclid.Basic
import Mathlib.Analysis.Calculus.Rademacher

/-! # Lipschitz data in the weighted completion

The convex-domain smoothing sequence for a Lipschitz function has uniformly
bounded gradients.  Its unweighted gradient convergence supplies an almost
everywhere convergent subsequence; the integrable coefficient trace then
dominates the weighted quadratic energies.
-/

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

private theorem hasWeakGradientOn_of_lipschitzOn
    {u : Vec d → ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K u V) :
    ∃ g : Vec d → ℝ, LipschitzWith K g ∧ Set.EqOn u g V ∧
      HasWeakGradientOn V u (fun x i => lineDeriv ℝ g x (basisVec i)) := by
  obtain ⟨g, hglob, hEq⟩ := hLip.extend_real
  refine ⟨g, hglob, hEq, ?_⟩
  intro i φ hφ hc hs
  obtain ⟨Dφ, hφlip⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hIBP := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume)
    hglob hφlip hc (basisVec i)
  have hnegφ (x : Vec d) : lineDeriv ℝ φ x (-basisVec i) =
      -(fderiv ℝ φ x) (basisVec i) := by
    rw [(hφ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
      (v := -basisVec i), map_neg]
  have hwhole :
      (∫ x, (fderiv ℝ φ x) (basisVec i) * g x) =
        -(∫ x, lineDeriv ℝ g x (basisVec i) * φ x) := by
    calc
      _ = -(∫ x, lineDeriv ℝ φ x (-basisVec i) * g x) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        rw [hnegφ]
        ring
      _ = -(∫ x, lineDeriv ℝ g x (basisVec i) * φ x) := by rw [hIBP]
  have hderivSupport :
      tsupport (fun x => (fderiv ℝ φ x) (basisVec i)) ⊆ tsupport φ :=
    tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := φ) (basisVec i)
  change (∫ x in V, u x * (fderiv ℝ φ x) (basisVec i) ∂volume) =
      -(∫ x in V, lineDeriv ℝ g x (basisVec i) * φ x ∂volume)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · calc
      (∫ x, u x * (fderiv ℝ φ x) (basisVec i)) =
          ∫ x, (fderiv ℝ φ x) (basisVec i) * g x := by
            apply integral_congr_ae
            filter_upwards with x
            by_cases hx : x ∈ V
            · rw [hEq hx]
              ring
            · have hzero : (fderiv ℝ φ x) (basisVec i) = 0 :=
                image_eq_zero_of_notMem_tsupport (f := fun y =>
                  (fderiv ℝ φ y) (basisVec i)) (fun hx' => hx (hs (hderivSupport hx')))
              rw [hzero]
              simp
      _ = -(∫ x, lineDeriv ℝ g x (basisVec i) * φ x) := hwhole
  · intro x hx
    have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (f := φ)
      (fun hx' => hx (hs hx'))
    simp only [hzero, mul_zero]
  · intro x hx
    have hzero : (fderiv ℝ φ x) (basisVec i) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y =>
        (fderiv ℝ φ y) (basisVec i)) (fun hx' => hx (hs (hderivSupport hx')))
    simp only [hzero, mul_zero]

private theorem weightedEnergy_lt_top_of_eNorm2_bound
    (ha : IsWeightedCoeffOn V a) {F : Vec d → Vec d}
    (hF : AEStronglyMeasurable F (volume.restrict V)) {M : ℝ}
    (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂(volume.restrict V),
      Foundations.Euclid.eNorm2 (F x) ≤ M) :
    weightedEnergy a V F < ⊤ := by
  have hqmeas := quadratic_aestronglyMeasurable ha hF
  have hqpos := quadratic_nonneg ha F
  have hqint : IntegrableOn
      (fun x => vecDot (F x) (matVecMul (a x) (F x))) V := by
    refine (ha.2.2.1.mul_const (M ^ 2)).mono' hqmeas ?_
    filter_upwards [ha.2.1, hbound, hqpos] with x hax hFx hq
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    calc
      vecDot (F x) (matVecMul (a x) (F x))
          ≤ (a x).trace * vecDot (F x) (F x) :=
            quadratic_le_trace_mul_length_sq (a x) hax (F x)
      _ ≤ (a x).trace * M ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hax.posSemidef.trace_nonneg
        change vecNormSq (F x) ≤ M ^ 2
        have hs := (sq_le_sq₀ (Foundations.Euclid.eNorm2_nonneg (F x)) hM).mpr hFx
        rw [Foundations.Euclid.eNorm2, Real.sq_sqrt (vecNormSq_nonneg _)] at hs
        exact hs
    
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
    hqmeas hqpos).mpr hqint)

private theorem weightedEnergy_tendsto_zero_of_dominated_gradient
    (ha : IsWeightedCoeffOn V a) {F : ℕ → Vec d → Vec d} {G : Vec d → Vec d}
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (hG : AEStronglyMeasurable G (volume.restrict V))
    {M : ℝ} (hM : 0 ≤ M)
    (hFbound : ∀ n, ∀ᵐ x ∂(volume.restrict V),
      Foundations.Euclid.eNorm2 (F n x) ≤ M)
    (hGbound : ∀ᵐ x ∂(volume.restrict V),
      Foundations.Euclid.eNorm2 (G x) ≤ M)
    (hlim : ∀ᵐ x ∂(volume.restrict V),
      Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0) := by
  let q : ℕ → Vec d → ℝ := fun n x =>
    vecDot (F n x - G x) (matVecMul (a x) (F n x - G x))
  let μ : Measure (Vec d) := volume.restrict V
  have hdiff : ∀ n, AEStronglyMeasurable (F n - G) μ :=
    fun n => (hF n).sub hG
  have hqmeas : ∀ n, AEStronglyMeasurable (q n) μ := by
    intro n
    exact quadratic_aestronglyMeasurable ha (hdiff n)
  have hqpos : ∀ n, 0 ≤ᵐ[μ] q n := by
    intro n
    simpa [q] using quadratic_nonneg ha (F n - G)
  let C : ℝ := 4 * M ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ n, ∀ᵐ x ∂μ, ‖q n x‖ ≤ C * (a x).trace := by
    intro n
    filter_upwards [ha.2.1, hFbound n, hGbound, hqpos n] with x hax hFx hGx hq
    have hdiffnorm : Foundations.Euclid.eNorm2 (F n x - G x) ≤ 2 * M := by
      calc
        _ = Foundations.Euclid.eNorm2 (F n x + -G x) := by rw [sub_eq_add_neg]
        _ ≤ Foundations.Euclid.eNorm2 (F n x) + Foundations.Euclid.eNorm2 (-G x) :=
          Foundations.Euclid.eNorm2_add_le _ _
        _ ≤ 2 * M := by
          rw [show Foundations.Euclid.eNorm2 (-G x) = Foundations.Euclid.eNorm2 (G x) by
            simpa using Foundations.Euclid.eNorm2_smul (-1) (G x)]
          linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hq]
    change vecDot (F n x - G x) (matVecMul (a x) (F n x - G x)) ≤ C * (a x).trace
    calc
      vecDot (F n x - G x) (matVecMul (a x) (F n x - G x))
          ≤ (a x).trace * vecDot (F n x - G x) (F n x - G x) :=
            quadratic_le_trace_mul_length_sq (a x) hax _
      _ ≤ (a x).trace * (2 * M) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hax.posSemidef.trace_nonneg
        have hs := (sq_le_sq₀
          (Foundations.Euclid.eNorm2_nonneg (F n x - G x)) (by linarith)).mpr hdiffnorm
        rw [Foundations.Euclid.eNorm2, Real.sq_sqrt (vecNormSq_nonneg _)] at hs
        exact hs
      _ = C * (a x).trace := by dsimp [C]; ring
  have hdom : Integrable (fun x => C * (a x).trace) μ := by
    simpa [μ, mul_comm] using ha.2.2.1.const_mul C
  have hq_lim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    have hcont : Continuous (fun z : Vec d =>
        vecDot (z - G x) (matVecMul (a x) (z - G x))) := by
      unfold vecDot matVecMul
      fun_prop
    simpa [q, Function.comp_def, vecDot_zero_left] using
      (hcont.continuousAt.tendsto.comp hx)
  have hreal : Tendsto (fun n => ∫ x, q n x ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence
      (fun x => C * (a x).trace) hqmeas hdom hbound hq_lim
  have hfinite : ∀ n, weightedEnergy a V (F n - G) < ⊤ := by
    intro n
    have hqint : IntegrableOn (q n) V := by
      refine hdom.mono' (hqmeas n) ?_
      filter_upwards [hbound n, hqpos n, ha.2.1] with x hb hq hax
      rw [Real.norm_eq_abs, abs_of_nonneg hq]
      rw [Real.norm_eq_abs, abs_of_nonneg hq] at hb
      exact hb
    exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable
      (quadratic_aestronglyMeasurable ha (hdiff n)) (quadratic_nonneg ha (F n - G))).mpr hqint)
  have henergy_eq (n : ℕ) :
      weightedEnergy a V (F n - G) = ENNReal.ofReal (∫ x, q n x ∂μ) := by
    have hE := hfinite n
    rw [← ENNReal.ofReal_toReal hE.ne, energy_toReal ha (hdiff n)]
    simp [q, μ]
  have hE : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hreal
    simpa [henergy_eq] using this
  exact hE

/-- A Lipschitz function on a bounded open convex domain belongs to the
weighted completion with any specified a.e. classical gradient. -/
theorem memH1a_of_lipschitzOn
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    {K : ℝ≥0}
    (hLip : LipschitzOnWith K u V)
    (hG : smoothGrad u =ᵐ[volume.restrict V] G) :
    MemH1a a V u G := by
  classical
  obtain ⟨g, hglob, hEq, hweak⟩ := hasWeakGradientOn_of_lipschitzOn hLip
  let μ : Measure (Vec d) := volume.restrict V
  let D : Vec d → Vec d := fun x i => lineDeriv ℝ g x (basisVec i)
  let : IsFiniteMeasure μ := by simpa [μ] using hV.isFiniteMeasure_restrict_volume
  have hDcoord : ∀ i : Fin d, MemLp (fun x => D x i) 1 μ := by
    intro i
    refine MemLp.of_bound (aestronglyMeasurable_lineDeriv hglob.continuous μ)
      (K : ℝ) ?_
    filter_upwards with x
    have hb := norm_lineDeriv_le_of_lipschitz ℝ hglob (x₀ := x) (v := basisVec i)
    have hi : ‖basisVec i‖ = 1 := by simp [basisVec, Pi.norm_single]
    simpa [D, hi] using hb
  have hDmem : MemLp D 1 μ := memLp_pi_iff.mpr hDcoord
  have hDmeas : AEStronglyMeasurable D μ := hDmem.aestronglyMeasurable
  have hDae : smoothGrad u =ᵐ[μ] D := by
    have hdiff : ∀ᵐ x ∂μ, DifferentiableAt ℝ g x := by
      rw [ae_restrict_iff' hV.isOpen.measurableSet]
      filter_upwards [hglob.ae_differentiableAt] with x hx _
      exact hx
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet, hdiff] with x hxV hdx
    have hlocal : u =ᶠ[𝓝 x] g := by
      filter_upwards [hV.isOpen.mem_nhds hxV] with y hy
      exact hEq hy
    have huD : HasFDerivAt u (fderiv ℝ g x) x :=
      hdx.hasFDerivAt.congr_of_eventuallyEq hlocal
    have hfd : fderiv ℝ u x = fderiv ℝ g x := huD.fderiv
    funext i
    change (fderiv ℝ u x) (basisVec i) = lineDeriv ℝ g x (basisVec i)
    calc
      _ = (fderiv ℝ g x) (basisVec i) := congrArg (fun L : StrongDual ℝ (Vec d) => L (basisVec i)) hfd
      _ = lineDeriv ℝ g x (basisVec i) := hdx.lineDeriv_eq_fderiv (v := basisVec i) |>.symm
  have hgmeas : AEStronglyMeasurable g μ :=
    hglob.continuous.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have huEq : u =ᵐ[μ] g := by
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    exact hEq hx
  have huMem : MemLp u 1 μ := by
    have hcl : IsCompact (closure V) :=
      hV.isBoundedDomain.isBounded.isCompact_closure
    obtain ⟨B, hB⟩ :=
      hcl.exists_bound_of_continuousOn hglob.continuous.continuousOn
    have hgMem : MemLp g 1 μ := by
      refine MemLp.of_bound hgmeas B ?_
      rw [ae_restrict_iff' hV.isOpen.measurableSet]
      exact Eventually.of_forall fun x hx => hB x (subset_closure hx)
    exact MeasureTheory.MemLp.ae_eq huEq.symm hgMem
  have hM : 0 ≤ Real.sqrt (d : ℝ) * (K : ℝ) := by positivity
  have hDbound : ∀ᵐ x ∂μ,
      Foundations.Euclid.eNorm2 (D x) ≤ Real.sqrt (d : ℝ) * (K : ℝ) := by
    filter_upwards with x
    have hcoord : ∀ i, ‖D x i‖ ≤ (K : ℝ) := by
      intro i
      have hb := norm_lineDeriv_le_of_lipschitz ℝ hglob (x₀ := x) (v := basisVec i)
      simpa [D, basisVec, Pi.norm_single] using hb
    have hpi : ‖D x‖ ≤ (K : ℝ) :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => hcoord i)
    exact (Foundations.Euclid.eNorm2_le_sqrt_mul_norm (D x)).trans
      (mul_le_mul_of_nonneg_left hpi (Real.sqrt_nonneg _))
  have hGmeas : AEStronglyMeasurable G μ := hDmeas.congr (hDae.symm.trans hG)
  have hGbound : ∀ᵐ x ∂μ,
      Foundations.Euclid.eNorm2 (G x) ≤ Real.sqrt (d : ℝ) * (K : ℝ) := by
    filter_upwards [hDbound, hDae.symm.trans hG] with x hDx hEqx
    rw [← hEqx]
    exact hDx
  rcases hne with ⟨x0, hx0⟩
  obtain ⟨δ, hδ, hball0⟩ := Metric.isOpen_iff.mp hV.isOpen x0 hx0
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hball : Metric.closedBall x0 r ⊆ V := by
    exact (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hball0
  have hp1 : 1 ≤ (1 : ℝ≥0∞) := le_rfl
  have hpTop : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
  let ρ : Vec d → ℝ := unitConvexApproxKernel
  let e : ℕ → ℝ := fun n => unitConvexApproxScale (n + 1)
  let ψ : ℕ → W1pFunction V (1 : ℝ≥0∞) :=
    fun n => W1pFunction.convexApproxSmoothW1p hV hp1
      ⟨u, D, huMem, fun i => hDcoord i, hweak⟩ x0 hr (n + 1)
  let f : ℕ → Vec d → ℝ := fun n =>
    convexApproxSmoothRepresentative V ρ u x0 r (e n)
  have he_pos : ∀ n, 0 < e n := by
    intro n
    simpa [e] using W1pFunction.unitConvexApproxScale_pos (n + 1)
  have he_lt : ∀ n, e n < 1 := by
    intro n
    simp only [e, unitConvexApproxScale]
    rw [div_lt_one (by positivity)]
    push_cast
    linarith
  have hf_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) := by
    intro n
    exact contDiff_convexApproxSmoothRepresentative hV.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp1 huMem hr (he_pos n)
  have hf_eq : ∀ n, ∀ x ∈ V,
      f n x = convexApproxSmoothing ρ u x0 r (e n) x := by
    intro n x hx
    exact convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hV
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hx hball hr (he_pos n) (he_lt n)
  have hpsi_value : ∀ n, (ψ n).toFun = f n := by
    intro n
    funext x
    simp [ψ, f, e, ρ, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
  have hLipApprox : ∀ n, LipschitzOnWith K (f n) V := by
    intro n
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hsmooth (z : Vec d) (hz : z ∈ V) :
        f n z = convexApproxSmoothing ρ g x0 r (e n) z := by
      rw [hf_eq n z hz]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (isClosed_tsupport ρ).measurableSet] with w hw
      simp only [convexApproxIntegrand_apply]
      have hsample : convexApproxSample x0 w r (e n) z ∈ V :=
        convexApproxSample_mem_of_tsupport_subset_closedBall hV hz hball
          (by simpa only [ρ] using
            (isConvexApproxKernel_unitConvexApproxKernel (d := d)).support_subset_closedBall)
          hw hr.le (he_pos n).le (he_lt n).le
      rw [hEq hsample]
    rw [Real.dist_eq, dist_eq_norm]
    rw [hsmooth x hx, hsmooth y hy]
    have hIx : IntegrableOn
        (fun z => ρ z * g (convexApproxSample x0 z r (e n) x)) (tsupport ρ) := by
      exact (integrable_convexApproxIntegrand
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)).continuous
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport
        hglob.continuous x0 r (e n) x).integrableOn
    have hIy : IntegrableOn
        (fun z => ρ z * g (convexApproxSample x0 z r (e n) y)) (tsupport ρ) := by
      exact (integrable_convexApproxIntegrand
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)).continuous
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport
        hglob.continuous x0 r (e n) y).integrableOn
    have hI : IntegrableOn
        (fun z => ρ z * (g (convexApproxSample x0 z r (e n) x) -
          g (convexApproxSample x0 z r (e n) y))) (tsupport ρ) := by
      convert hIx.sub hIy using 1
      funext z
      simp only [Pi.sub_apply, mul_sub]
    have hsub :
        (∫ z in tsupport ρ, ρ z * g (convexApproxSample x0 z r (e n) x)) -
          ∫ z in tsupport ρ, ρ z * g (convexApproxSample x0 z r (e n) y) =
        ∫ z in tsupport ρ, ρ z * (g (convexApproxSample x0 z r (e n) x) -
          g (convexApproxSample x0 z r (e n) y)) := by
      rw [← integral_sub hIx hIy]
      apply integral_congr_ae
      filter_upwards with z
      ring
    simp only [convexApproxSmoothing, convexApproxIntegrand]
    rw [hsub]
    change ‖∫ z in tsupport ρ, ρ z *
      (g (convexApproxSample x0 z r (e n) x) -
        g (convexApproxSample x0 z r (e n) y))‖ ≤ (K : ℝ) * ‖x - y‖
    have hdist (z : Vec d) :
        ‖convexApproxSample x0 z r (e n) x -
          convexApproxSample x0 z r (e n) y‖ =
          |1 - e n| * ‖x - y‖ := by
      have heq : convexApproxSample x0 z r (e n) x -
          convexApproxSample x0 z r (e n) y = (1 - e n) • (x - y) := by
        unfold convexApproxSample
        module
      rw [heq, norm_smul, Real.norm_eq_abs]
    calc
      ‖∫ z in tsupport ρ, ρ z *
          (g (convexApproxSample x0 z r (e n) x) -
            g (convexApproxSample x0 z r (e n) y))‖
          ≤ ∫ z in tsupport ρ, ‖ρ z *
              (g (convexApproxSample x0 z r (e n) x) -
                g (convexApproxSample x0 z r (e n) y))‖ :=
              norm_integral_le_integral_norm _
      _ ≤ ∫ z in tsupport ρ, ρ z * ((K : ℝ) * ‖x - y‖) := by
        apply integral_mono_ae hI.norm
          ((integrable_convexApproxKernelMulConst
            (isConvexApproxKernel_unitConvexApproxKernel (d := d)).continuous
            (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport
            ((K : ℝ) * ‖x - y‖)).integrableOn)
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
          ((isConvexApproxKernel_unitConvexApproxKernel (d := d)).nonneg z)]
        apply mul_le_mul_of_nonneg_left _
          ((isConvexApproxKernel_unitConvexApproxKernel (d := d)).nonneg z)
        calc
          |g (convexApproxSample x0 z r (e n) x) -
              g (convexApproxSample x0 z r (e n) y)|
              ≤ (K : ℝ) * ‖convexApproxSample x0 z r (e n) x -
                convexApproxSample x0 z r (e n) y‖ :=
                  hglob.dist_le_mul _ _
          _ = (K : ℝ) * (|1 - e n| * ‖x - y‖) := by rw [hdist]
          _ ≤ (K : ℝ) * ‖x - y‖ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_of_le_one_left (norm_nonneg _)
            rw [abs_of_nonneg (by linarith [he_lt n])]
            linarith [he_pos n]
      _ = (K : ℝ) * ‖x - y‖ := by
        rw [MeasureTheory.integral_mul_const]
        rw [show (∫ z in tsupport ρ, ρ z) = 1 by
          exact (isConvexApproxKernel_unitConvexApproxKernel (d := d)).setIntegral_one]
        ring
    
  have hgradBound : ∀ n, ∀ᵐ x ∂μ,
      Foundations.Euclid.eNorm2 (smoothGrad (f n) x) ≤ Real.sqrt (d : ℝ) * (K : ℝ) := by
    intro n
    rw [ae_restrict_iff' hV.isOpen.measurableSet]
    exact Eventually.of_forall fun x hx => by
      have hfd : ‖fderiv ℝ (f n) x‖ ≤ (K : ℝ) :=
        norm_fderiv_le_of_lipschitzOn ℝ (hV.isOpen.mem_nhds hx) (hLipApprox n)
      have hcoord : ∀ i, ‖smoothGrad (f n) x i‖ ≤ (K : ℝ) := by
        intro i
        exact (ContinuousLinearMap.le_opNorm (fderiv ℝ (f n) x) (basisVec i)).trans
          (by simpa [basisVec, Pi.norm_single] using hfd)
      have hpi : ‖smoothGrad (f n) x‖ ≤ (K : ℝ) :=
        (pi_norm_le_iff_of_nonneg (by positivity)).2 hcoord
      exact (Foundations.Euclid.eNorm2_le_sqrt_mul_norm _).trans
        (mul_le_mul_of_nonneg_left hpi (Real.sqrt_nonneg _))
  have hcore : ∀ n, IsSmoothCore a V (f n) := by
    intro n
    have hmeas := smoothGrad_aestronglyMeasurable hV.isOpen (hf_smooth n).contDiffOn
    have hfinite := weightedEnergy_lt_top_of_eNorm2_bound ha hmeas hM (hgradBound n)
    refine ⟨(hf_smooth n).contDiffOn, ?_, hfinite⟩
    have hi : Integrable ((ψ n).toFun) μ := (ψ n).memLp.integrable le_rfl
    simpa only [hpsi_value n, μ, IntegrableOn] using hi
  have hval : Tendsto
      (fun n => eLpNorm (f n - u) 1 μ) atTop (𝓝 0) := by
    simpa [ψ, f, e, ρ, μ, volumeMeasureOn, Function.comp_def,
      W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain, Pi.sub_def] using
      (W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
        hV hp1 hpTop ⟨u, D, huMem, fun i => hDcoord i, hweak⟩ hball hr).comp (tendsto_add_atTop_nat 1)
  have hcoord : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => smoothGrad (f n) x i - D x i) 1 μ)
      atTop (𝓝 0) := by
    intro i
    simpa [ψ, f, e, ρ, μ, volumeMeasureOn, Function.comp_def,
      smoothGrad, CoarseDeGiorgi.smoothGrad, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain] using
      (W1pFunction.tendsto_convexApproxSmoothW1p_grad_eLpNorm_sub
        hV hp1 hpTop ⟨u, D, huMem, fun i => hDcoord i, hweak⟩ hball hr i).comp (tendsto_add_atTop_nat 1)
  have hvec : Tendsto
      (fun n => eLpNorm (smoothGrad (f n) - D) 1 μ) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n => ∑ i : Fin d,
        eLpNorm (fun x => smoothGrad (f n) x i - D x i) 1 μ) atTop (𝓝 0) := by
      have h := tendsto_finsetSum (s := Finset.univ)
        (f := fun i n => eLpNorm (fun x => smoothGrad (f n) x i - D x i) 1 μ)
        (a := fun _ => 0) (fun i _ => hcoord i)
      simpa using h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => bot_le)
    intro n
    have hpoint : ∀ x, ‖smoothGrad (f n) x - D x‖ ≤
        ∑ i : Fin d, |smoothGrad (f n) x i - D x i| := by
      intro x
      have hs : 0 ≤ ∑ i : Fin d, |smoothGrad (f n) x i - D x i| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      apply (pi_norm_le_iff_of_nonneg hs).2
      intro i
      change |smoothGrad (f n) x i - D x i| ≤ _
      exact Finset.single_le_sum
        (f := fun j => |smoothGrad (f n) x j - D x j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hmeas : AEStronglyMeasurable (smoothGrad (f n) - D) μ :=
      (smoothGrad_aestronglyMeasurable hV.isOpen (hf_smooth n).contDiffOn).sub hDmeas
    calc
      eLpNorm (smoothGrad (f n) - D) 1 μ
          ≤ eLpNorm (fun x => ∑ i : Fin d,
              |smoothGrad (f n) x i - D x i|) 1 μ :=
            eLpNorm_mono_real hmeas hpoint
      _ ≤ ∑ i : Fin d, eLpNorm (fun x => |smoothGrad (f n) x i - D x i|) 1 μ := by
        convert
          (eLpNorm_sum_le (p := 1) (μ := μ) (s := Finset.univ)
            (f := fun i x => |smoothGrad (f n) x i - D x i|) le_rfl) using 1
        congr 1
        funext x
        simp
      _ = ∑ i : Fin d, eLpNorm (fun x => smoothGrad (f n) x i - D x i) 1 μ := by
        apply Finset.sum_congr rfl
        intro i _
        have hm : AEStronglyMeasurable
            (fun x => smoothGrad (f n) x i - D x i) μ :=
          (continuous_apply i).comp_aestronglyMeasurable hmeas
        simpa only [Real.norm_eq_abs] using
          (eLpNorm_norm (fun x => smoothGrad (f n) x i - D x i) hm)
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (f := fun n => smoothGrad (f n)) (g := D)
    (by norm_num : (1 : ℝ≥0∞) ≠ 0) hvec
  obtain ⟨σ, hσmono, hσae⟩ := hmeasure.exists_seq_tendsto_ae
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun n => smoothGrad (f (σ n)) x) atTop (𝓝 (G x)) := by
    filter_upwards [hσae, hDae.symm.trans hG] with x hx hEqx
    simpa only [hEqx] using hx
  have henergy := weightedEnergy_tendsto_zero_of_dominated_gradient ha
    (fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hf_smooth (σ n)).contDiffOn)
    hGmeas hM (fun n => hgradBound (σ n)) hGbound hlim
  have hvalσ : Tendsto (fun n => eLpNorm (f (σ n) - u) 1 μ) atTop (𝓝 0) :=
    hval.comp hσmono.tendsto_atTop
  exact memH1a_of_core_tendsto hV ha (fun n => hcore (σ n)) (huMem.integrable le_rfl) hGmeas hvalσ henergy


end CoarseDeGiorgi.Weighted
