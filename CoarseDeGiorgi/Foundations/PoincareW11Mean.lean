module

public import Homogenization.CoarseGraining.Definitions
public import Homogenization.Sobolev.Foundations.PoincareLp
public import Homogenization.Sobolev.Foundations.PoincareW1p
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing

@[expose] public section

namespace CoarseDeGiorgi.Foundations

open Homogenization MeasureTheory
open scoped ENNReal

private theorem norm_linearMap_le_sum_basisVec
    {d : ℕ} (L : Vec d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin d, |L (basisVec i)| := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ => abs_nonneg _) ?_
  intro x
  have hx : L x = ∑ i : Fin d, x i * L (basisVec i) := by
    calc
      L x = ∑ i : Fin d, x i * L (fun j => if i = j then 1 else 0) := by
        simpa using (LinearMap.pi_apply_eq_sum_univ (f := L.toLinearMap) x)
      _ = ∑ i : Fin d, x i * L (basisVec i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hfun : (fun j => if i = j then 1 else 0) = basisVec i := by
          funext j
          simp [basisVec_apply, eq_comm]
        rw [hfun]
  calc
    ‖L x‖ = ‖∑ i : Fin d, x i * L (basisVec i)‖ := by rw [hx]
    _ ≤ ∑ i : Fin d, ‖x i * L (basisVec i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin d, |x i| * |L (basisVec i)| := by simp [Real.norm_eq_abs]
    _ ≤ ∑ i : Fin d, ‖x‖ * |L (basisVec i)| := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (norm_le_pi_norm x i) (abs_nonneg _)
    _ = (∑ i : Fin d, |L (basisVec i)|) * ‖x‖ := by
      rw [Finset.sum_mul]
      simp [mul_comm]

private theorem sum_abs_le_dim_mul_euclideanLength
    {d : ℕ} (G : Vec d) :
    (∑ i : Fin d, |G i|) ≤ (d : ℝ) * Real.sqrt (vecDot G G) := by
  have hi (i : Fin d) : |G i| ≤ Real.sqrt (vecDot G G) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (sq_apply_le_vecNormSq G i)
  calc
    (∑ i : Fin d, |G i|) ≤ ∑ i : Fin d, Real.sqrt (vecDot G G) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = (d : ℝ) * Real.sqrt (vecDot G G) := by simp

private theorem tendsto_eLpNorm_abs_sub_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {f : α → ℝ}
    (hF : ∀ n, MemLp (F n) 1 μ) (hf : MemLp f 1 μ)
    (h : Filter.Tendsto (fun n => eLpNorm (F n - f) 1 μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => eLpNorm (fun x => |F n x| - |f x|) 1 μ)
      Filter.atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => bot_le)
  intro n
  apply eLpNorm_mono_ae ((hF n).norm.sub hf.norm).aestronglyMeasurable
  filter_upwards with x
  simpa [Real.norm_eq_abs] using abs_abs_sub_abs_le_abs_sub (F n x) (f x)

private theorem smooth_mean_zero_poincare_w11
    {d : ℕ} [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hvol : 0 < (volume V).toReal)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    let C := ((volume V).toReal⁻¹ *
      (((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ))) *
        ((d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hV.isBoundedDomain))
    ∫ x in V, |f x - volumeAverage V f| ∂volume ≤
      C * ∫ x in V, ∑ i : Fin d, |(fderiv ℝ f x) (basisVec i)| ∂volume := by
  classical
  let μ : Measure (Vec d) := volume.restrict V
  let D : Vec d → Vec d := fun x i => (fderiv ℝ f x) (basisVec i)
  let g : Vec d → ℝ := fun x => ‖fderiv ℝ f x‖
  let S : Vec d → ℝ := fun x => ∑ i : Fin d, |D x i|
  let K : ℝ := ((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ)
  let M : ℝ := (d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
    (4 * Classical.choose hV.isBoundedDomain)
  let B : ℝ := (volume V).toReal⁻¹ * K
  let C : ℝ := B * M
  let : IsFiniteMeasure (volumeMeasureOn V) := by
    simpa [volumeMeasureOn] using hV.isFiniteMeasure_restrict_volume
  have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hR : 0 < Classical.choose hV.isBoundedDomain :=
    (Classical.choose_spec hV.isBoundedDomain).1
  have hB : 0 ≤ B := by dsimp [B, K]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hkernel : IntegrableOn (fun z : Vec d × Vec d => rieszKernel z.1 z.2)
      (V ×ˢ V) (volume.prod volume) :=
    integrableOn_prod_rieszKernel_of_isSobolevRegularDomain hV.isSobolevRegularDomain
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hderiv_cont : Continuous (fderiv ℝ f) := hf1.continuous_fderiv (by norm_num)
  have hprod : IntegrableOn
      (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2)
      (V ×ˢ V) (volume.prod volume) := by
    have hcont : ContinuousOn (fun z : Vec d × Vec d => ‖fderiv ℝ f z.2‖)
        (closure V ×ˢ closure V) :=
      (continuous_norm.comp (hderiv_cont.comp continuous_snd)).continuousOn
    have hcompact : IsCompact (closure V ×ˢ closure V) :=
      hV.isBoundedDomain.isBounded.isCompact_closure.prod
        hV.isBoundedDomain.isBounded.isCompact_closure
    have hsub : V ×ˢ V ⊆ closure V ×ˢ closure V := by
      intro z hz
      exact ⟨subset_closure hz.1, subset_closure hz.2⟩
    simpa [g, mul_comm] using
      hkernel.mul_continuousOn_of_subset hcont
        (hV.isOpen.measurableSet.prod hV.isOpen.measurableSet) hcompact hsub
  have hprod' : Integrable
      (fun z : Vec d × Vec d => g z.2 * rieszKernel z.1 z.2) (μ.prod μ) := by
    simpa [μ, IntegrableOn, Measure.prod_restrict] using hprod
  have hpot : Integrable (fun x => ∫ y, g y * rieszKernel x y ∂μ) μ :=
    hprod'.integral_prod_left
  have hleft : Integrable (fun x => |f x - volumeAverage V f|) μ := by
    have hcont : Continuous (fun x => |f x - volumeAverage V f|) :=
      (hf.continuous.sub continuous_const).abs
    exact (hcont.continuousOn.integrableOn_compact
      hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  have hpoint :
      (fun x => |f x - volumeAverage V f|) ≤ᵐ[μ]
        (fun x => B * ∫ y, g y * rieszKernel x y ∂μ) := by
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with x hx
    have h := norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_rieszKernel_of_isOpenBoundedConvexDomain
      hV (by
        have hcont := hf.continuous
        exact (hcont.continuousOn.integrableOn_compact
          hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure) hf hx hvol
    simpa [B, K, g, μ, Real.norm_eq_abs, volumeAverage, integralAverage,
      MeasureTheory.IntegrableOn, mul_assoc] using h
  have hupper : Integrable (fun x => B * ∫ y, g y * rieszKernel x y ∂μ) μ :=
    hpot.const_mul B
  have hboundInt := MeasureTheory.integral_mono_ae hleft hupper hpoint
  have hswapInt : Integrable (fun y => ∫ x, g y * rieszKernel x y ∂μ) μ :=
    hprod'.integral_prod_right
  have hgInt : Integrable g μ := by
    have hcont : Continuous g := continuous_norm.comp hderiv_cont
    exact (hcont.continuousOn.integrableOn_compact
      hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  have hscaledInt : Integrable (fun y => g y * M) μ := hgInt.mul_const M
  have hswapBound :
      (fun y => ∫ x, g y * rieszKernel x y ∂μ) ≤ᵐ[μ] fun y => g y * M := by
    filter_upwards [ae_restrict_mem hV.isOpen.measurableSet] with y hy
    have hg : 0 ≤ g y := norm_nonneg _
    have hkr : ∫ x, rieszKernel x y ∂μ ≤ M := by
      simpa [μ, M, IntegrableOn] using
        hV.isBoundedDomain.integral_rieszKernel_right_le hy
    calc
      ∫ x, g y * rieszKernel x y ∂μ = g y * ∫ x, rieszKernel x y ∂μ :=
        integral_const_mul _ _
      _ ≤ g y * M := mul_le_mul_of_nonneg_left hkr hg
  have hswapBoundInt := MeasureTheory.integral_mono_ae hswapInt hscaledInt hswapBound
  have hgradInt : Integrable S μ := by
    have hcont : Continuous S := by
      unfold S D
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact
      hV.isBoundedDomain.isBounded.isCompact_closure).mono_set subset_closure
  have hg_le : g ≤ᵐ[μ] S := by
    filter_upwards with x
    calc
      g x ≤ ∑ i : Fin d, |(fderiv ℝ f x) (basisVec i)| :=
        norm_linearMap_le_sum_basisVec _
      _ = S x := by rfl
  have hgradBound := MeasureTheory.integral_mono_ae hgInt hgradInt hg_le
  have hgeom :
      ∫ x, |f x - volumeAverage V f| ∂μ ≤ C * ∫ x, S x ∂μ := by
    calc
      ∫ x, |f x - volumeAverage V f| ∂μ ≤
          ∫ x, B * (∫ y, g y * rieszKernel x y ∂μ) ∂μ := hboundInt
      _ = B * ∫ x, ∫ y, g y * rieszKernel x y ∂μ ∂μ := by
        rw [integral_const_mul]
      _ = B * ∫ y, ∫ x, g y * rieszKernel x y ∂μ ∂μ := by
        congr 1
        exact integral_integral_swap hprod'
      _ ≤ B * ∫ y, g y * M ∂μ :=
        mul_le_mul_of_nonneg_left hswapBoundInt hB
      _ = B * M * ∫ y, g y ∂μ := by
        rw [integral_mul_const]
        ring
      _ ≤ C * ∫ y, S y ∂μ := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_left hgradBound (mul_nonneg hB hM)
  simpa [C, B, M, K, S, D, μ, volumeAverage, integralAverage] using hgeom

/-- The convex-domain mean-zero Poincare inequality at exponent one.  Its
constant is the same Riesz-potential constant as in the smooth proof, times
the dimension factor converting coordinate variation to Euclidean length. -/
theorem mean_zero_poincare_w11_of_w1p
    {d : ℕ} [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (u : W1pFunction V (1 : ENNReal)) :
    let C := ((volume V).toReal⁻¹ *
      (((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ))) *
        ((d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hV.isBoundedDomain)) * (d : ℝ)
    ∫ x in V, |u.toFun x - volumeAverage V u.toFun| ∂volume ≤
      C * ∫ x in V, Real.sqrt (vecDot (u.grad x) (u.grad x)) ∂volume := by
  classical
  let μ : Measure (Vec d) := volume.restrict V
  let : IsFiniteMeasure μ := by
    simpa [μ] using hV.isFiniteMeasure_restrict_volume
  have hpos : 0 < (volume V).toReal := by
    have hp := hV.isOpen.measure_pos volume hne
    exact ENNReal.toReal_pos hp.ne' hV.volume_lt_top.ne
  rcases hne with ⟨x0, hx0⟩
  rcases Metric.mem_nhds_iff.1 (hV.isOpen.mem_nhds hx0) with ⟨δ, hδ, hδsub⟩
  let r : ℝ := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hball : Metric.closedBall x0 r ⊆ V := by
    intro y hy
    apply hδsub
    have hy' : dist y x0 ≤ r := by simpa [Metric.mem_closedBall] using hy
    have hlt : dist y x0 < δ := by
      have hrδ : r < δ := by dsimp [r]; linarith
      exact lt_of_le_of_lt hy' hrδ
    simpa [Metric.mem_ball] using hlt
  have hp1 : 1 ≤ (1 : ENNReal) := le_rfl
  have hpTop : (1 : ENNReal) ≠ ⊤ := by norm_num
  let ψ : ℕ → W1pFunction V (1 : ENNReal) :=
    fun n => W1pFunction.convexApproxSmoothW1p hV hp1 u x0 hr n
  let f : ℕ → Vec d → ℝ := fun n =>
    convexApproxSmoothRepresentative V (unitConvexApproxKernel (d := d))
      u.toFun x0 r (unitConvexApproxScale n)
  have hψ_bound : ∀ n,
      ∫ x in V, |(ψ n).toFun x - volumeAverage V (ψ n).toFun| ∂volume ≤
        (((volume V).toReal⁻¹ *
          (((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ))) *
          ((d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
            (4 * Classical.choose hV.isBoundedDomain))) *
          ∫ x in V, ∑ i : Fin d, |(fderiv ℝ (f n) x) (basisVec i)| ∂volume := by
    intro n
    have hf : ContDiff ℝ (⊤ : ℕ∞) (f n) :=
      contDiff_convexApproxSmoothRepresentative
        (U := V) (ρ := unitConvexApproxKernel (d := d)) (u := u.toFun)
        (p := (1 : ENNReal)) (x0 := x0) (r := r)
        (ε := unitConvexApproxScale n) hV.isOpen.measurableSet
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp1 u.memLp hr
        (W1pFunction.unitConvexApproxScale_pos n)
    simpa [ψ, f, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain] using
      smooth_mean_zero_poincare_w11 hV hpos hf
  have hval : Filter.Tendsto
      (fun n => eLpNorm (fun x => (ψ n).toFun x - u.toFun x) 1 μ)
      Filter.atTop (nhds 0) := by
    simpa [ψ, μ, volumeMeasureOn] using
      W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
        hV hp1 hpTop u hball hr
  have hgrad : ∀ i : Fin d, Filter.Tendsto
      (fun n => eLpNorm (fun x => (ψ n).grad x i - u.grad x i) 1 μ)
      Filter.atTop (nhds 0) := by
    intro i
    simpa [ψ, μ, volumeMeasureOn] using
      W1pFunction.tendsto_convexApproxSmoothW1p_grad_eLpNorm_sub
        hV hp1 hpTop u hball hr i
  have hψint : ∀ n, Integrable (ψ n).toFun μ :=
    fun n => ((ψ n).memLp).integrable le_rfl
  have havgIntegral : Filter.Tendsto
      (fun n => ∫ x, (ψ n).toFun x ∂μ)
      Filter.atTop (nhds (∫ x, u.toFun x ∂μ)) :=
    MeasureTheory.tendsto_integral_of_L1' (f := u.toFun) (F := fun n => (ψ n).toFun)
      (Filter.Eventually.of_forall hψint) hval
  have havg : Filter.Tendsto
      (fun n => volumeAverage V (ψ n).toFun)
      Filter.atTop (nhds (volumeAverage V u.toFun)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (volume V).toReal⁻¹)
        Filter.atTop (nhds ((volume V).toReal⁻¹)) := tendsto_const_nhds
    have hmul := hconst.mul havgIntegral
    simpa [volumeAverage, μ] using hmul
  have havgDiff : Filter.Tendsto
      (fun n => volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)
      Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => volumeAverage V u.toFun)
        Filter.atTop (nhds (volumeAverage V u.toFun)) := tendsto_const_nhds
    simpa using hconst.sub havg
  have hconstLp : Filter.Tendsto
      (fun n => eLpNorm
        (fun _ : Vec d => volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)
        1 μ) Filter.atTop (nhds 0) := by
    have henorm : Filter.Tendsto
        (fun n => ‖volumeAverage V u.toFun - volumeAverage V (ψ n).toFun‖ₑ)
        Filter.atTop (nhds 0) := by
      simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
        ENNReal.tendsto_ofReal havgDiff.norm
    have hmeasure : μ Set.univ < ⊤ := MeasureTheory.measure_lt_top μ Set.univ
    have hscaled := ENNReal.Tendsto.mul_const henorm (Or.inr hmeasure.ne)
    have hformula : (fun n => eLpNorm
        (fun _ : Vec d => volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)
        1 μ) = fun n =>
          ‖volumeAverage V u.toFun - volumeAverage V (ψ n).toFun‖ₑ * μ Set.univ := by
      funext n
      simpa using (eLpNorm_const' (μ := μ) (p := (1 : ENNReal))
        (c := volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)
        (by norm_num) (by norm_num))
    simpa [hformula] using hscaled
  have hcenter : Filter.Tendsto
      (fun n => eLpNorm (fun x =>
        ((ψ n).toFun x - volumeAverage V (ψ n).toFun) -
          (u.toFun x - volumeAverage V u.toFun)) 1 μ)
      Filter.atTop (nhds 0) := by
    have hsum : Filter.Tendsto
        (fun n => eLpNorm (fun x => (ψ n).toFun x - u.toFun x) 1 μ +
          eLpNorm (fun _ : Vec d => volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)
            1 μ) Filter.atTop (nhds 0) := by
      simpa using hval.add hconstLp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => bot_le)
    intro n
    have hA : MemLp (fun x => (ψ n).toFun x - u.toFun x) 1 μ :=
      (ψ n).memLp.sub u.memLp
    have hB : MemLp
        (fun _ : Vec d => volumeAverage V u.toFun - volumeAverage V (ψ n).toFun) 1 μ :=
      memLp_const (volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)
    calc
      eLpNorm (fun x =>
          ((ψ n).toFun x - volumeAverage V (ψ n).toFun) -
            (u.toFun x - volumeAverage V u.toFun)) 1 μ =
        eLpNorm ((fun x => (ψ n).toFun x - u.toFun x) +
          (fun _ : Vec d => volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)) 1 μ := by
            apply eLpNorm_congr_ae
            filter_upwards with x
            simp only [Pi.add_apply, sub_eq_add_neg]
            abel
      _ ≤ eLpNorm (fun x => (ψ n).toFun x - u.toFun x) 1 μ +
          eLpNorm (fun _ : Vec d => volumeAverage V u.toFun - volumeAverage V (ψ n).toFun)
            1 μ := eLpNorm_add_le le_rfl
  have hcenterAbs : Filter.Tendsto
      (fun n => eLpNorm (fun x => |(ψ n).toFun x - volumeAverage V (ψ n).toFun| -
        |u.toFun x - volumeAverage V u.toFun|) 1 μ)
      Filter.atTop (nhds 0) := by
    have hFn : ∀ n, MemLp (fun x => (ψ n).toFun x - volumeAverage V (ψ n).toFun) 1 μ := by
      intro n
      exact (ψ n).memLp.sub (memLp_const _)
    have hF : MemLp (fun x => u.toFun x - volumeAverage V u.toFun) 1 μ :=
      u.memLp.sub (memLp_const _)
    simpa [Real.norm_eq_abs] using
      tendsto_eLpNorm_abs_sub_zero hFn hF hcenter
  have hcenterAbsInt : Filter.Tendsto
      (fun n => ∫ x, |(ψ n).toFun x - volumeAverage V (ψ n).toFun| ∂μ)
      Filter.atTop (nhds (∫ x, |u.toFun x - volumeAverage V u.toFun| ∂μ)) := by
    have hFi : ∀ n, Integrable
        (fun x => |(ψ n).toFun x - volumeAverage V (ψ n).toFun|) μ := by
      intro n
      exact ((ψ n).memLp.sub (memLp_const _)).integrable le_rfl |>.norm
    exact MeasureTheory.tendsto_integral_of_L1'
      (f := fun x => |u.toFun x - volumeAverage V u.toFun|)
      (F := fun n x => |(ψ n).toFun x - volumeAverage V (ψ n).toFun|)
      (Filter.Eventually.of_forall hFi) hcenterAbs
  let D : ℕ → Vec d → Vec d := fun n x i => (fderiv ℝ (f n) x) (basisVec i)
  have hDgrad : ∀ n x i, D n x i = (ψ n).grad x i := by
    intro n x i
    simp [D, ψ, f, W1pFunction.convexApproxSmoothW1p,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
      W1pFunction.ofContDiffOnIsSobolevRegularDomain]
  have hgradD : ∀ i : Fin d, Filter.Tendsto
      (fun n => eLpNorm (fun x => D n x i - u.grad x i) 1 μ)
      Filter.atTop (nhds 0) := by
    intro i
    simpa [D, hDgrad] using hgrad i
  have hDmem : ∀ n i, MemLp (fun x => D n x i) 1 μ := by
    intro n i
    simpa [hDgrad] using (ψ n).gradMemLp i
  have hgradAbsInt : ∀ i : Fin d, Filter.Tendsto
      (fun n => ∫ x, |D n x i| ∂μ)
      Filter.atTop (nhds (∫ x, |u.grad x i| ∂μ)) := by
    intro i
    have habs := tendsto_eLpNorm_abs_sub_zero (fun n => hDmem n i)
      (u.gradMemLp i) (hgradD i)
    have hFi : ∀ n, Integrable (fun x => |D n x i|) μ := by
      intro n
      exact (hDmem n i).integrable le_rfl |>.norm
    exact MeasureTheory.tendsto_integral_of_L1'
      (f := fun x => |u.grad x i|) (F := fun n x => |D n x i|)
      (Filter.Eventually.of_forall hFi) habs
  have hgradSumAbs : Filter.Tendsto
      (fun n => ∫ x, ∑ i : Fin d, |D n x i| ∂μ)
      Filter.atTop (nhds (∫ x, ∑ i : Fin d, |u.grad x i| ∂μ)) := by
    have hsum := tendsto_finsetSum (s := Finset.univ) (f := fun i n => ∫ x, |D n x i| ∂μ)
      (a := fun i => ∫ x, |u.grad x i| ∂μ) (fun i hi => hgradAbsInt i)
    have happroxSum : ∀ n,
        (∫ x, ∑ i : Fin d, |D n x i| ∂μ) =
          ∑ i : Fin d, ∫ x, |D n x i| ∂μ := by
      intro n
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i hi => (hDmem n i).integrable le_rfl |>.norm)
    have htargetSum :
        (∫ x, ∑ i : Fin d, |u.grad x i| ∂μ) =
          ∑ i : Fin d, ∫ x, |u.grad x i| ∂μ := by
      exact MeasureTheory.integral_finsetSum Finset.univ
        (fun i hi => (u.gradMemLp i).integrable le_rfl |>.norm)
    simpa [happroxSum, htargetSum] using hsum
  have hleft : Filter.Tendsto
      (fun n => ∫ x, |(ψ n).toFun x - volumeAverage V (ψ n).toFun| ∂μ)
      Filter.atTop (nhds (∫ x, |u.toFun x - volumeAverage V u.toFun| ∂μ)) := by
    simpa [μ] using hcenterAbsInt
  have hrightCoord : Filter.Tendsto
      (fun n =>
        (((volume V).toReal⁻¹ *
          (((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ))) *
          ((d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
            (4 * Classical.choose hV.isBoundedDomain))) *
          (∫ x, ∑ i : Fin d, |D n x i| ∂μ))
      Filter.atTop (nhds (
        (((volume V).toReal⁻¹ *
          (((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ))) *
          ((d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
            (4 * Classical.choose hV.isBoundedDomain))) *
          (∫ x, ∑ i : Fin d, |u.grad x i| ∂μ))) := by
    exact tendsto_const_nhds.mul hgradSumAbs
  have hlimit := le_of_tendsto_of_tendsto' hleft hrightCoord hψ_bound
  have hsumInt : Integrable (fun x => ∑ i : Fin d, |u.grad x i|) μ := by
    simpa using MeasureTheory.integrable_finsetSum (μ := μ) Finset.univ
      (fun i hi => (u.gradMemLp i).integrable le_rfl |>.norm)
  have hlen_meas : AEStronglyMeasurable
      (fun x => Real.sqrt (vecDot (u.grad x) (u.grad x))) μ := by
    have hvec : AEStronglyMeasurable u.grad μ :=
      (memLp_pi_iff.mpr u.gradMemLp).aestronglyMeasurable
    have hcont : Continuous (fun G : Vec d => Real.sqrt (vecDot G G)) := by
      unfold vecDot
      fun_prop
    exact hcont.comp_aestronglyMeasurable hvec
  have hlen_le_sum (G : Vec d) :
      Real.sqrt (vecDot G G) ≤ ∑ i : Fin d, |G i| := by
    have hsumSq : vecDot G G ≤ (∑ i : Fin d, |G i|) ^ 2 := by
      calc
        vecDot G G = ∑ i : Fin d, |G i| ^ 2 := by
          simp [vecDot, pow_two]
        _ ≤ (∑ i : Fin d, |G i|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
            (f := fun i => |G i|) (fun i hi => abs_nonneg (G i))
    calc
      Real.sqrt (vecDot G G) ≤ Real.sqrt ((∑ i : Fin d, |G i|) ^ 2) :=
        Real.sqrt_le_sqrt hsumSq
      _ = abs (∑ i : Fin d, |G i|) := Real.sqrt_sq_eq_abs _
      _ = ∑ i : Fin d, |G i| := by
        rw [abs_of_nonneg (Finset.sum_nonneg (s := Finset.univ)
          (fun i hi => abs_nonneg (G i)))]
  have hlenInt : Integrable (fun x => Real.sqrt (vecDot (u.grad x) (u.grad x))) μ := by
    refine hsumInt.mono' hlen_meas ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hlen_le_sum (u.grad x)
  have hsumLeLen :
      ∫ x, ∑ i : Fin d, |u.grad x i| ∂μ ≤
        (d : ℝ) * ∫ x, Real.sqrt (vecDot (u.grad x) (u.grad x)) ∂μ := by
    calc
      ∫ x, ∑ i : Fin d, |u.grad x i| ∂μ ≤
          ∫ x, (d : ℝ) * Real.sqrt (vecDot (u.grad x) (u.grad x)) ∂μ := by
            apply MeasureTheory.integral_mono_ae hsumInt (hlenInt.const_mul (d : ℝ))
            filter_upwards with x
            exact sum_abs_le_dim_mul_euclideanLength (u.grad x)
      _ = (d : ℝ) * ∫ x, Real.sqrt (vecDot (u.grad x) (u.grad x)) ∂μ :=
        by rw [MeasureTheory.integral_const_mul]
  have hCnonneg : 0 ≤ (((volume V).toReal⁻¹ *
      (((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ))) *
      ((d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
        (4 * Classical.choose hV.isBoundedDomain))) := by
    have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
    have hR : 0 < Classical.choose hV.isBoundedDomain :=
      (Classical.choose_spec hV.isBoundedDomain).1
    have hballtoReal : 0 ≤ (volume (Metric.ball (0 : Vec d) 1)).toReal :=
      ENNReal.toReal_nonneg
    positivity
  have hfinal := hlimit.trans (mul_le_mul_of_nonneg_left hsumLeLen hCnonneg)
  simpa [μ, mul_assoc] using hfinal

/-- Raw-function form of the convex-domain mean-zero Poincare inequality in
`W^{1,1}`. -/
theorem exists_mean_zero_poincare_w11
    {d : ℕ} [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
        IntegrableOn u V →
        (∀ i : Fin d, IntegrableOn (fun x => G x i) V) →
        HasWeakGradientOn V u G →
        ∫ x in V, |u x - volumeAverage V u| ∂volume ≤
          C * ∫ x in V, Real.sqrt (vecDot (G x) (G x)) ∂volume := by
  classical
  let C := ((volume V).toReal⁻¹ *
      (((2 * Classical.choose hV.isBoundedDomain) ^ d) / (d : ℝ))) *
        ((d : ℝ) * (volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hV.isBoundedDomain)) * (d : ℝ)
  have hCnonneg : 0 ≤ C := by
    have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
    have hR : 0 < Classical.choose hV.isBoundedDomain :=
      (Classical.choose_spec hV.isBoundedDomain).1
    have hvol : 0 ≤ (volume V).toReal := ENNReal.toReal_nonneg
    have hball : 0 ≤ (volume (Metric.ball (0 : Vec d) 1)).toReal :=
      ENNReal.toReal_nonneg
    dsimp [C]
    positivity
  refine ⟨C, hCnonneg, ?_⟩
  intro u G hu hGi hweak
  let w : W1pFunction V (1 : ENNReal) :=
    { toFun := u
      grad := G
      memLp := memLp_one_iff_integrable.mpr hu
      gradMemLp := fun i => memLp_one_iff_integrable.mpr (hGi i)
      hasWeakGradient := hweak }
  have h := mean_zero_poincare_w11_of_w1p hV hne w
  simpa [w, C] using h

end CoarseDeGiorgi.Foundations
