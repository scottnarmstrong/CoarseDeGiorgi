module

public import Homogenization.Sobolev.Truncation.Approx
public import Homogenization.Sobolev.W1p.WeakGradientClosure
public import Mathlib.MeasureTheory.Function.UniformIntegrable

@[expose] public section

namespace CoarseDeGiorgi.Foundations

open Homogenization
open MeasureTheory Filter Topology
open scoped ENNReal

theorem hasWeakGradientOn_tendsto_setIntegral_mul_of_tendsto_eLpNorm_one
    {d : ℕ} {U : Set (Vec d)} {h : Vec d → ℝ}
    {f : ℕ → Vec d → ℝ} {g : Vec d → ℝ}
    (hh : MemLp h ⊤ (volume.restrict U))
    (hf : ∀ n, MemLp (f n) 1 (volume.restrict U))
    (hg : MemLp g 1 (volume.restrict U))
    (htend : Tendsto (fun n => eLpNorm (f n - g) 1 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, f n x * h x ∂volume) atTop
      (𝓝 (∫ x in U, g x * h x ∂volume)) := by
  let _ : ENNReal.HolderConjugate (1 : ℝ≥0∞) ⊤ := ENNReal.HolderConjugate.one_top
  let μ : Measure (Vec d) := volume.restrict U
  have hfh_int : ∀ n, Integrable (fun x => f n x * h x) μ := by
    intro n
    simpa [μ, mul_comm] using
      (memLp_one_iff_integrable.mp (hh.fun_mul (hf n)))
  have hgh_int : Integrable (fun x => g x * h x) μ := by
    simpa [μ, mul_comm] using (memLp_one_iff_integrable.mp (hh.fun_mul hg))
  rw [← tendsto_sub_nhds_zero_iff]
  have hdiff_eq : ∀ n,
      (∫ x, f n x * h x ∂μ) - (∫ x, g x * h x ∂μ) =
        ∫ x, (f n x - g x) * h x ∂μ := by
    intro n
    rw [← integral_sub (hfh_int n) hgh_int]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  let B : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm (f n - g) 1 μ * eLpNorm h ⊤ μ
  have hBtend : Tendsto (fun n => (B n).toReal) atTop (𝓝 0) := by
    have hprod : Tendsto B atTop (𝓝 (0 * eLpNorm h ⊤ μ)) := by
      refine ENNReal.Tendsto.mul (by simpa [B, μ] using htend)
        (Or.inr hh.eLpNorm_ne_top) tendsto_const_nhds (Or.inr (by simp))
    rw [zero_mul] at hprod
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hprod
    convert hreal using 1 <;> ext n <;> rfl
  refine squeeze_zero_norm ?_ hBtend
  intro n
  rw [hdiff_eq n]
  have hbound : ∀ᵐ x ∂μ,
      ‖(f n x - g x) * h x‖₊ ≤ 1 * ‖f n x - g x‖₊ * ‖h x‖₊ :=
    Eventually.of_forall fun x => by rw [nnnorm_mul]; simp
  have hHolder : eLpNorm (fun x => (f n x - g x) * h x) 1 μ ≤ B n := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := (1 : ℝ≥0∞)) (q := ⊤) (r := (1 : ℝ≥0∞))
      (fun a b : ℝ => a * b) 1 continuous_mul
      ((hf n).sub hg).aestronglyMeasurable hh.aestronglyMeasurable hbound
    simpa [B] using h
  calc
    ‖∫ x, (f n x - g x) * h x ∂μ‖
      ≤ (∫⁻ x, ENNReal.ofReal ‖(f n x - g x) * h x‖ ∂μ).toReal :=
        norm_integral_le_lintegral_norm (fun x => (f n x - g x) * h x)
    _ = (∫⁻ x, ‖(f n x - g x) * h x‖ₑ ∂μ).toReal := by
      congr 1
      refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [Real.enorm_eq_ofReal_abs]
    _ = (eLpNorm (fun x => (f n x - g x) * h x) 1 μ).toReal := by
      change (∫⁻ x, ‖((f n x - g x) * h x)‖ₑ ∂μ).toReal =
        (eLpNorm ((f n - g) * h) 1 μ).toReal
      rw [eLpNorm_one_eq_lintegral_enorm
        (((hf n).sub hg).aestronglyMeasurable.mul hh.aestronglyMeasurable)]
      simp [μ]
    _ ≤ (B n).toReal := by
      apply ENNReal.toReal_mono _ hHolder
      exact ENNReal.mul_ne_top ((hf n).sub hg).eLpNorm_lt_top.ne hh.eLpNorm_ne_top

theorem hasWeakPartialDerivOn_of_tendsto_eLpNorm_one
    {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} {u_n g_n : ℕ → Vec d → ℝ}
    (hu : MemLp u 1 (volume.restrict U)) (hgi : MemLp gi 1 (volume.restrict U))
    (hu_n : ∀ n, MemLp (u_n n) 1 (volume.restrict U))
    (hg_n : ∀ n, MemLp (g_n n) 1 (volume.restrict U))
    (hweak : ∀ n, HasWeakPartialDerivOn U i (u_n n) (g_n n))
    (htend_u : Tendsto (fun n => eLpNorm (u_n n - u) 1 (volume.restrict U)) atTop (𝓝 0))
    (htend_g : Tendsto (fun n => eLpNorm (g_n n - gi) 1 (volume.restrict U)) atTop (𝓝 0)) :
    HasWeakPartialDerivOn U i u gi := by
  intro φ hφ hφ_compact hφ_sub
  let μ : Measure (Vec d) := volume.restrict U
  have hDφ : MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) ⊤ μ := by
    have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
      (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcs : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      apply HasCompactSupport.mono' (hφ_compact.fderiv ℝ)
      intro x hx
      apply subset_tsupport (fderiv ℝ φ)
      rw [Function.mem_support] at hx ⊢
      intro h0
      apply hx
      rw [h0]
      simp
    exact hcont.memLp_top_of_hasCompactSupport hcs μ
  have hφmem : MemLp φ ⊤ μ := hφ.continuous.memLp_top_of_hasCompactSupport hφ_compact μ
  have hlhs := hasWeakGradientOn_tendsto_setIntegral_mul_of_tendsto_eLpNorm_one
    hDφ hu_n hu htend_u
  have hrhs := hasWeakGradientOn_tendsto_setIntegral_mul_of_tendsto_eLpNorm_one
    hφmem hg_n hgi htend_g
  have heq_n : ∀ n,
      (∫ x in U, u_n n x * (fderiv ℝ φ x) (basisVec i) ∂volume) =
        -(∫ x in U, g_n n x * φ x ∂volume) := fun n => hweak n φ hφ hφ_compact hφ_sub
  have hlhs' : Tendsto
      (fun n => -(∫ x in U, g_n n x * φ x ∂volume)) atTop
      (𝓝 (∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume)) := by
    refine hlhs.congr ?_
    intro n
    rw [heq_n n]
  have hlim := tendsto_nhds_unique hlhs' hrhs.neg
  simpa using hlim

/-! ### The `C¹` chain rule on bounded open convex domains -/

/-- **`W^{1,1}` chain rule.** A `C¹` scalar map with bounded derivative sends
an `L¹` function and its `L¹` weak gradient to the pointwise chain-rule
gradient. -/
theorem hasWeakGradientOn_comp_of_deriv_bounded_w11
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U 1 u) (hDu : GradMemLpOn U 1 Du)
    (hweak : HasWeakGradientOn U u Du)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {M : ℝ} (hM : 0 ≤ M) (hderiv : ∀ t, |deriv Φ t| ≤ M) :
    HasWeakGradientOn U (fun x => Φ (u x))
      (fun x i => deriv Φ (u x) * Du x i) := by
  have hΦdiff : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hΦlip : LipschitzWith M.toNNReal Φ := lipschitzWith_of_abs_deriv_le hM hΦdiff hderiv
  let μ : Measure (Vec d) := volume.restrict U
  let _ : IsFiniteMeasure μ := by
    simpa [μ] using hU.isFiniteMeasure_restrict_volume
  have hp1 : 1 ≤ (1 : ℝ≥0∞) := by norm_num
  have hpTop : (1 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rcases U.eq_empty_or_nonempty with hempty | hne
  · subst U
    intro i φ hφ hφc hφs
    simp
  obtain ⟨x0, hx0U⟩ := hne
  obtain ⟨r0, hr0, hball0⟩ := Metric.isOpen_iff.mp hU.isOpen x0 hx0U
  let r : ℝ := r0 / 2
  have hr : 0 < r := by positivity
  have hball : Metric.closedBall x0 r ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball0
    dsimp [r]
    linarith
  let ρ : Vec d → ℝ := unitConvexApproxKernel
  have hρ : IsConvexApproxKernel ρ := isConvexApproxKernel_unitConvexApproxKernel
  let e : ℕ → ℝ := fun n => unitConvexApproxScale (n + 1)
  have he_pos : ∀ n, 0 < e n := by
    intro n
    simp only [e, unitConvexApproxScale]
    positivity
  have he_lt : ∀ n, e n < 1 := by
    intro n
    simp only [e, unitConvexApproxScale]
    rw [div_lt_one (by positivity)]
    have hn : (0 : ℝ) ≤ n := by positivity
    push_cast
    linarith
  let w : ℕ → Vec d → ℝ := fun n =>
    convexApproxSmoothRepresentative U ρ u x0 r (e n)
  have hw_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (w n) := by
    intro n
    exact contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet hρ hp1 hu hr
      (he_pos n)
  have hw_eq : ∀ n, ∀ x ∈ U,
      w n x = unitConvexApproxSequence u x0 r (n + 1) x := by
    intro n x hx
    simpa [w, unitConvexApproxSequence, e, ρ] using
      (convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU hρ hx hball hr
        (he_pos n) (he_lt n))
  have hcompMem : ∀ v : Vec d → ℝ, MemLp v 1 μ →
      MemLp (fun x => Φ (v x)) 1 μ := by
    intro v hv
    have hΦ0lip : LipschitzWith M.toNNReal (fun t => Φ t - Φ 0) := by
      intro a b
      simpa [edist_sub_right] using hΦlip a b
    have h1 : MemLp (fun x => Φ (v x) - Φ 0) 1 μ :=
      hΦ0lip.comp_memLp (by simp) hv
    have h2 : MemLp (fun _ : Vec d => Φ 0) 1 μ := memLp_const _
    refine (h1.add h2).ae_eq ?_
    filter_upwards with x
    simp
  have hderivCont : Continuous (deriv Φ) := hΦ.continuous_deriv (by norm_num)
  have haesmDeriv : ∀ v : Vec d → ℝ, AEStronglyMeasurable v μ →
      AEStronglyMeasurable (fun x => deriv Φ (v x)) μ :=
    fun v hv => hderivCont.comp_aestronglyMeasurable hv
  intro i
  let Dwn : ℕ → Vec d → ℝ := fun n x => (fderiv ℝ (w n) x) (basisVec i)
  let un : ℕ → Vec d → ℝ := fun n x => Φ (w n x)
  let gn : ℕ → Vec d → ℝ := fun n x => deriv Φ (w n x) * Dwn n x
  let smi : ℕ → Vec d → ℝ := fun n =>
    convexApproxSmoothing ρ (fun y => Du y i) x0 r (e n)
  have hweak_n : ∀ n, HasWeakPartialDerivOn U i (un n) (gn n) := by
    intro n
    have hΦwn : ContDiff ℝ 1 (fun x => Φ (w n x)) :=
      hΦ.comp ((hw_smooth n).of_le (by norm_num))
    have h := (HasWeakGradientOn.of_contDiff (U := U) hΦwn) i
    have hEq :
        (fun x => (fderiv ℝ (fun y => Φ (w n y)) x) (basisVec i)) = gn n := by
      funext x
      rw [fderiv_comp_basisVec hΦdiff.differentiableAt
        ((hw_smooth n).differentiable (by norm_num)).differentiableAt]
    simpa [un] using hEq ▸ h
  have hbridge : ∀ n, Dwn n =ᵐ[μ] (fun x => (1 - e n) * smi n x) := by
    intro n
    have h := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec hU hρ hp1 hu
      (hDu i) (hweak i) hball hr (he_pos n) (he_lt n)
    filter_upwards [h, ae_restrict_mem hU.isOpen.measurableSet] with x hdx hx
    dsimp [Dwn, smi]
    rw [hdx]
    rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU hρ hx hball hr
      (he_pos n) (he_lt n)]
    simp only [convexApproxSmoothing_apply, convexApproxIntegrand_apply,
      convexApproxSample]
  have hwn_mem : ∀ n, MemLp (w n) 1 μ := by
    intro n
    have hsm := memLpOn_convexApproxSmoothing hU hρ hp1 hpTop hu hball hr
      (he_pos n) (he_lt n)
    refine hsm.ae_eq ?_
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    simpa [w, unitConvexApproxSequence, e, ρ] using (hw_eq n x hx).symm
  have hun_mem : ∀ n, MemLp (un n) 1 μ := fun n => hcompMem (w n) (hwn_mem n)
  have hsmi_mem : ∀ n, MemLp (smi n) 1 μ := by
    intro n
    simpa [smi] using
      memLpOn_convexApproxSmoothing hU hρ hp1 hpTop (hDu i) hball hr (he_pos n) (he_lt n)
  have hDwn_mem : ∀ n, MemLp (Dwn n) 1 μ := by
    intro n
    exact ((hsmi_mem n).const_mul (1 - e n)).ae_eq (hbridge n).symm
  have hgn_mem : ∀ n, MemLp (gn n) 1 μ := by
    intro n
    refine MemLp.of_le ((hDwn_mem n).const_mul M) ?_ ?_
    · exact (haesmDeriv (w n) (hw_smooth n).continuous.aestronglyMeasurable).mul
        (hDwn_mem n).aestronglyMeasurable
    · filter_upwards with x
      simp only [gn, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (by rw [abs_of_nonneg hM]; exact hderiv (w n x)) (abs_nonneg _)
  have hΦu_mem : MemLp (fun x => Φ (u x)) 1 μ := hcompMem u hu
  have htarget_mem : MemLp (fun x => deriv Φ (u x) * Du x i) 1 μ := by
    refine MemLp.of_le ((hDu i).const_mul M) ?_ ?_
    · exact (haesmDeriv u hu.aestronglyMeasurable).mul (hDu i).aestronglyMeasurable
    · filter_upwards with x
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (by rw [abs_of_nonneg hM]; exact hderiv (u x)) (abs_nonneg _)
  have hwu : Tendsto
      (fun n => eLpNorm (fun x => w n x - u x) 1 μ) atTop (𝓝 0) := by
    have hbase := tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
      hU hp1 hpTop hu hball hr
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    refine hshift.congr (fun n => ?_)
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    rw [hw_eq n x hx]
  obtain ⟨σ, hσ_mono, hσ_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hwu).exists_seq_tendsto_ae
  have hDwn_conv : Tendsto
      (fun n => eLpNorm (fun x => Dwn n x - Du x i) 1 μ) atTop (𝓝 0) := by
    have hbase := tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
      hU hp1 hpTop (hDu i) hball hr
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    refine hshift.congr (fun n => ?_)
    apply eLpNorm_congr_ae
    filter_upwards [hbridge n] with x hx
    rw [hx]
    simp [smi, unitConvexApproxSequence, e, ρ]
  have hun_conv : Tendsto
      (fun k => eLpNorm (fun x => un (σ k) x - Φ (u x)) 1 μ) atTop (𝓝 0) := by
    have hle : ∀ k,
        eLpNorm (fun x => un (σ k) x - Φ (u x)) 1 μ ≤
          ENNReal.ofReal M * eLpNorm (fun x => w (σ k) x - u x) 1 μ := by
      intro k
      calc
        eLpNorm (fun x => Φ (w (σ k) x) - Φ (u x)) 1 μ
            ≤ eLpNorm (fun x => M • (w (σ k) x - u x)) 1 μ := by
                apply eLpNorm_mono
                  ((hΦlip.continuous.comp_aestronglyMeasurable
                    (hw_smooth (σ k)).continuous.aestronglyMeasurable).sub
                    (hΦlip.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable))
                intro x
                have hdist := hΦlip.dist_le_mul (w (σ k) x) (u x)
                rw [norm_smul]
                simp only [Real.norm_eq_abs, abs_of_nonneg hM]
                simpa [Real.dist_eq, Real.coe_toNNReal M hM] using hdist
        _ = ENNReal.ofReal M * eLpNorm (fun x => w (σ k) x - u x) 1 μ := by
              rw [show (fun x => M • (w (σ k) x - u x)) =
                M • (fun x => w (σ k) x - u x) from rfl, eLpNorm_const_smul]
              simp [Real.enorm_eq_ofReal hM]
    have hrhs : Tendsto
        (fun k => ENNReal.ofReal M * eLpNorm (fun x => w (σ k) x - u x) 1 μ)
        atTop (𝓝 0) := by
      have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M)
        (hwu.comp hσ_mono.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
      simpa using ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun _ => zero_le) hle
  let TB : ℕ → Vec d → ℝ := fun k x =>
    (deriv Φ (w (σ k) x) - deriv Φ (u x)) * Du x i
  have hTB_meas : ∀ k, AEStronglyMeasurable (TB k) μ := by
    intro k
    exact ((haesmDeriv (w (σ k)) (hw_smooth (σ k)).continuous.aestronglyMeasurable).sub
      (haesmDeriv u hu.aestronglyMeasurable)).mul (hDu i).aestronglyMeasurable
  have hTB_dom : MemLp (fun x => (2 * M) * Du x i) 1 μ :=
    (hDu i).const_mul (2 * M)
  have hTB_ui : UnifIntegrable TB 1 μ := by
    apply (unifIntegrable_const hp1 hpTop hTB_dom).ae_mono hTB_meas
    intro k
    filter_upwards with x
    change ‖TB k x‖ₑ ≤ ‖(2 * M) * Du x i‖ₑ
    have hnorm : ‖TB k x‖ ≤ ‖(2 * M) * Du x i‖ := by
      simp only [TB, norm_mul, Real.norm_eq_abs]
      simp only [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_nonneg hM]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      calc
        |deriv Φ (w (σ k) x) - deriv Φ (u x)|
            ≤ |deriv Φ (w (σ k) x)| + |deriv Φ (u x)| := abs_sub _ _
        _ ≤ M + M := add_le_add (hderiv _) (hderiv _)
        _ = 2 * M := by ring
    simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using
      ENNReal.ofReal_le_ofReal hnorm
  have hTB_ae : ∀ᵐ x ∂μ, Tendsto (fun k => TB k x) atTop (𝓝 0) := by
    filter_upwards [hσ_ae] with x hx
    have h1 : Tendsto (fun k => deriv Φ (w (σ k) x)) atTop (𝓝 (deriv Φ (u x))) :=
      (hderivCont.tendsto _).comp hx
    have h2 := (h1.sub (tendsto_const_nhds (x := deriv Φ (u x)))).mul_const (Du x i)
    simpa [TB] using h2
  have hTB_conv : Tendsto (fun k => eLpNorm (TB k) 1 μ) atTop (𝓝 0) := by
    have h := tendsto_Lp_finite_of_tendsto_ae (p := (1 : ℝ≥0∞)) hp1 hpTop
      hTB_meas (memLp_const (0 : ℝ)) hTB_ui hTB_ae
    refine h.congr (fun k => ?_)
    apply eLpNorm_congr_ae
    filter_upwards with x
    simp
  have hTA_le : ∀ k, eLpNorm
      (fun x => deriv Φ (w (σ k) x) * (Dwn (σ k) x - Du x i)) 1 μ ≤
        ENNReal.ofReal M * eLpNorm (fun x => Dwn (σ k) x - Du x i) 1 μ := by
    intro k
    calc
      eLpNorm (fun x => deriv Φ (w (σ k) x) * (Dwn (σ k) x - Du x i)) 1 μ
          ≤ eLpNorm (fun x => M • (Dwn (σ k) x - Du x i)) 1 μ := by
              apply eLpNorm_mono
                ((haesmDeriv (w (σ k)) (hw_smooth (σ k)).continuous.aestronglyMeasurable).mul
                  ((hDwn_mem (σ k)).aestronglyMeasurable.sub
                    (hDu i).aestronglyMeasurable))
              intro x
              change ‖deriv Φ (w (σ k) x) * (Dwn (σ k) x - Du x i)‖ ≤
                ‖M • (Dwn (σ k) x - Du x i)‖
              rw [norm_mul, norm_smul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right
                (by simpa [Real.norm_eq_abs, abs_of_nonneg hM] using hderiv _)
                (abs_nonneg _)
      _ = ENNReal.ofReal M * eLpNorm (fun x => Dwn (σ k) x - Du x i) 1 μ := by
            rw [show (fun x => M • (Dwn (σ k) x - Du x i)) =
              M • (fun x => Dwn (σ k) x - Du x i) from rfl, eLpNorm_const_smul]
            simp [Real.enorm_eq_ofReal hM]
  have hTA_conv : Tendsto
      (fun k => eLpNorm
        (fun x => deriv Φ (w (σ k) x) * (Dwn (σ k) x - Du x i)) 1 μ)
      atTop (𝓝 0) := by
    have hrhs : Tendsto
        (fun k => ENNReal.ofReal M * eLpNorm (fun x => Dwn (σ k) x - Du x i) 1 μ)
        atTop (𝓝 0) := by
      have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M)
        (hDwn_conv.comp hσ_mono.tendsto_atTop) (Or.inr ENNReal.ofReal_ne_top)
      simpa using ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun _ => zero_le) hTA_le
  have hgn_conv : Tendsto
      (fun k => eLpNorm
        (fun x => gn (σ k) x - deriv Φ (u x) * Du x i) 1 μ) atTop (𝓝 0) := by
    have hsplit : ∀ k,
        eLpNorm (fun x => gn (σ k) x - deriv Φ (u x) * Du x i) 1 μ ≤
          eLpNorm (fun x => deriv Φ (w (σ k) x) * (Dwn (σ k) x - Du x i)) 1 μ +
            eLpNorm (TB k) 1 μ := by
      intro k
      have heq :
          (fun x => gn (σ k) x - deriv Φ (u x) * Du x i) =
            (fun x => deriv Φ (w (σ k) x) * (Dwn (σ k) x - Du x i) + TB k x) := by
        funext x
        simp only [gn, Dwn, TB]
        ring
      rw [heq]
      exact eLpNorm_add_le hp1
    have hsum : Tendsto
        (fun k => eLpNorm
            (fun x => deriv Φ (w (σ k) x) * (Dwn (σ k) x - Du x i)) 1 μ +
          eLpNorm (TB k) 1 μ) atTop (𝓝 0) := by
      simpa using hTA_conv.add hTB_conv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) hsplit
  exact hasWeakPartialDerivOn_of_tendsto_eLpNorm_one hΦu_mem htarget_mem
    (fun k => hun_mem (σ k)) (fun k => hgn_mem (σ k))
    (fun k => hweak_n (σ k)) hun_conv hgn_conv

end Foundations
