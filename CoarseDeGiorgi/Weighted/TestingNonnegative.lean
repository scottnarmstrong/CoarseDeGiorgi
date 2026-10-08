import CoarseDeGiorgi.Weighted.TestingApproximation

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- One-sided smooth positive-part approximants are nonnegative. -/
theorem GApprox_nonneg {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 ≤ GApprox 0 δ t := by
  by_cases ht : 0 ≤ t
  · exact intervalIntegral.integral_nonneg_of_forall ht (gStep_nonneg 0 δ)
  · have hzero : GApprox 0 δ t = 0 := by
      change (∫ s in (0 : ℝ)..t, gStep 0 δ s) = 0
      calc
        _ = ∫ _ in (0 : ℝ)..t, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_ge (le_of_not_ge ht)] at hs
          exact gStep_eq_zero hδ (by linarith only [hs.2, hδ])
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero]

/-- Positive-part representatives agree with a nonnegative pair almost everywhere. -/
theorem nonnegative_pair_posPart_ae (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x) :
    (fun x => max (u x) 0) =ᵐ[volume.restrict V] u ∧
      {x | 0 < u x}.indicator G =ᵐ[volume.restrict V] G := by
  refine ⟨hnonneg.mono (fun x hx => max_eq_left hx), ?_⟩
  filter_upwards [hnonneg, MemH1a.gradient_zero_on_level hV hne ha hu 0] with x hx hg
  by_cases hpos : 0 < u x
  · simp only [Set.mem_ofPred_eq, hpos, Set.indicator_of_mem]
  · have hz : u x = 0 := le_antisymm (le_of_not_gt hpos) hx
    have hGzero : G x = 0 := by simpa only [Set.mem_ofPred_eq, hz,
      Set.indicator_of_mem, eq_self] using hg
    rw [Set.indicator_of_notMem (show x ∉ {x | 0 < u x} from hpos), hGzero]

/-- Smooth scalar positive-part approximants converge to a nonnegative pair. -/
theorem nonnegative_GApprox_tendsto (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x) :
    Tendsto (fun n : ℕ => eLpNorm ((GApprox 0 (1 / (n + 1))) ∘ u - u)
      1 (volume.restrict V)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => weightedEnergy a V
      ((fun x => gStep 0 (1 / (n + 1)) (u x) • G x) - G)) atTop (𝓝 0) := by
  let μ := volume.restrict V
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδpos : ∀ n, 0 < δ n := by intro n; positivity
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hEG := MemH1a.energy_lt_top hV.isOpen ha hu
  have hGpos := (nonnegative_pair_posPart_ae hV hne ha hu hnonneg).2
  constructor
  · have hbound : Tendsto (fun n => ENNReal.ofReal (2 * δ n) * μ Set.univ)
        atTop (𝓝 0) := by
      have hf : μ Set.univ ≠ ⊤ := by
        simp only [μ, Measure.restrict_apply_univ]
        exact hV.isBoundedDomain.isBounded.measure_lt_top.ne
      simpa only [Function.comp_def, mul_zero, zero_mul, ENNReal.ofReal_zero] using
        ENNReal.Tendsto.mul_const (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (hδ.const_mul (2 : ℝ))) (Or.inr hf)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun _ => bot_le)
    intro n
    have htwo : 0 < 2 * δ n := mul_pos (by norm_num) (hδpos n)
    have hm := ((GApprox_contDiff_top 0 (δ n)).continuous.comp_aestronglyMeasurable hu.1).sub hu.1
    have hh := eLpNorm_mono_ae hm (g := fun _ : Vec d => (2 * δ n : ℝ))
      (hnonneg.mono fun x hx => by
        simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply,
          abs_of_pos htwo, sub_zero, max_eq_left hx]
          using abs_GApprox_sub_le (c := 0) (hδpos n) (u x)) (p := 1)
    simpa only [δ, μ, Function.comp_def, eLpNorm_const' _ (by norm_num : (1 : ENNReal) ≠ 0)
      (by norm_num : (1 : ENNReal) ≠ ⊤), ENNReal.toReal_one, one_div_one,
      ENNReal.rpow_one, Real.enorm_eq_ofReal_abs,
      abs_of_pos htwo] using hh
  · let χ : Vec d → ℝ := fun x => if 0 < u x then 1 else 0
    have hs : NullMeasurableSet {x | 0 < u x} μ :=
      nullMeasurableSet_lt measurable_const.aemeasurable hu.1.aemeasurable
    have hχ : AEStronglyMeasurable χ μ := aestronglyMeasurable_const.indicator₀ hs
    have hχG : (fun x => χ x • G x) =ᵐ[μ] G := by
      convert hGpos using 1
      funext x
      by_cases hx : 0 < u x <;> simp [χ, hx]
    have ht := tendsto_energy_mul_zero ha hu.2.1 hEG
      (b := fun n x => gStep 0 (δ n) (u x) - χ x)
      (fun n => ((gStep_continuous 0 (δ n)).comp_aestronglyMeasurable hu.1).sub hχ)
      (M := 2) (fun n => ?_) ?_
    · convert ht using 1
      funext n
      apply energy_congr_ae
      filter_upwards [hχG] with x hx
      simp only [Pi.sub_apply, sub_smul]
      rw [hx]
    · filter_upwards with x
      have h1 := gStep_nonneg 0 (δ n) (u x)
      have h2 := gStep_le_one 0 (δ n) (u x)
      dsimp [χ]
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith only [h1, h2]
    · filter_upwards with x
      simpa [χ] using (tendsto_gStep (c := 0) hδpos hδ (u x)).sub_const (χ x)

/-- Nonnegative members of the zero-boundary space have nonnegative supported
smooth approximants, with convergence in value L¹ and gradient energy. -/
theorem MemH1a0.nonnegative_approximation (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemH1a0 a V u G) (hnonneg : ∀ᵐ x ∂volume.restrict V, 0 ≤ u x) :
    ∃ f : ℕ → Vec d → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) ∧ HasCompactSupport (f n) ∧
        tsupport (f n) ⊆ V ∧ ∀ x, 0 ≤ f n x) ∧
      Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0) ∧
      Tendsto (fun n => weightedEnergy a V (smoothGrad (f n) - G)) atTop (𝓝 0) := by
  let S := {f : supportedCoreSubmodule V | ∀ x, 0 ≤ f.val x}
  let μ := volume.restrict V
  have hw := hu.memH1a ha
  have hi := (memH1a_memW11 hV hne ha hw).1
  let H := memH1aEnergyField hV.isOpen ha hw
  let target : Lp ℝ 1 μ × GradientHilbert ha :=
    ((memLp_one_iff_integrable.mpr hi).toLp u, (H : GradientHilbert ha))
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδpos : ∀ n, 0 < δ n := by intro n; positivity
  let v : ℕ → Vec d → ℝ := fun n => GApprox 0 (δ n) ∘ u
  let D : ℕ → Vec d → Vec d := fun n x => gStep 0 (δ n) (u x) • G x
  have hv (n : ℕ) : CoarseDeGiorgi.MemH1a a V (v n) (D n) := by
    simpa only [deriv_GApprox] using MemH1a.comp hV hne ha hw
      (GApprox_contDiff_top 0 (δ n)) (L := 1) (abs_deriv_GApprox_le 0 (δ n))
  let J : ℕ → GradientCore ha := fun n => memH1aEnergyField hV.isOpen ha (hv n)
  have hvi := fun n => (memH1a_memW11 hV hne ha (hv n)).1
  have hmem (n : ℕ) : ((memLp_one_iff_integrable.mpr (hvi n)).toLp (v n),
      (J n : GradientHilbert ha)) ∈ closure (supportedL1Graph hV.isOpen ha '' S) := by
    obtain ⟨f, hf, hr, hL, hE⟩ := MemH1a0.comp_approximation hV hne ha hu
      (GApprox_contDiff_top 0 (δ n)) (by simp [GApprox])
      (L := 1) (abs_deriv_GApprox_le 0 (δ n))
    have hg : Tendsto (fun k =>
        (smoothEnergyField hV.isOpen ha (isSmoothCore_of_supported ha (hf k).1 (hf k).2.1) :
          GradientHilbert ha)) atTop (𝓝 (J n : GradientHilbert ha)) :=
      GradientCore.tendsto_coe_of_energy ha
        (F := fun k => smoothEnergyField hV.isOpen ha
          (isSmoothCore_of_supported ha (hf k).1 (hf k).2.1)) (G := J n)
        (by change Tendsto (fun k => weightedEnergy a V (smoothGrad (f k) - D n)) atTop (𝓝 0)
            simpa only [D, deriv_GApprox] using hE)
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f
      (fun k => memLp_one_iff_integrable.mpr
        (isSmoothCore_of_supported ha (hf k).1 (hf k).2.1).2.1) (v n)
      (memLp_one_iff_integrable.mpr (hvi n))).mpr hL
    apply isClosed_closure.mem_of_tendsto (ht.prodMk_nhds hg)
    apply Eventually.of_forall
    intro k
    apply subset_closure
    refine ⟨⟨f k, hf k⟩, ?_, rfl⟩
    intro x
    change 0 ≤ f k x
    obtain ⟨t, ht⟩ := hr k x
    rw [ht]
    exact GApprox_nonneg (hδpos n) t
  obtain ⟨hL, hE⟩ := nonnegative_GApprox_tendsto hV hne ha hw hnonneg
  have htarget : target ∈ closure (supportedL1Graph hV.isOpen ha '' S) := by
    have hvlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v
      (fun n => memLp_one_iff_integrable.mpr (hvi n)) u
      (memLp_one_iff_integrable.mpr hi)).mpr hL
    have hglim := GradientCore.tendsto_coe_of_energy ha (F := J) (G := H) hE
    exact isClosed_closure.mem_of_tendsto (hvlim.prodMk_nhds hglim)
      (Eventually.of_forall hmem)
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp htarget
  choose f hf heq using hz
  have htf : Tendsto (fun n => supportedL1Graph hV.isOpen ha (f n)) atTop (𝓝 target) := by
    simpa only [heq] using ht
  have hvlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (f n).val)
    (fun n => memLp_one_iff_integrable.mpr
      (isSmoothCore_of_supported ha (f n).property.1 (f n).property.2.1).2.1) u
    (memLp_one_iff_integrable.mpr hi)).mp (continuous_fst.continuousAt.tendsto.comp htf)
  have hglim : Tendsto (fun n =>
      (smoothEnergyField hV.isOpen ha
        (isSmoothCore_of_supported ha (f n).property.1 (f n).property.2.1) : GradientHilbert ha))
      atTop (𝓝 (H : GradientHilbert ha)) := continuous_snd.continuousAt.tendsto.comp htf
  exact ⟨fun n => (f n).val, fun n => ⟨(f n).property.1, (f n).property.2.1,
    (f n).property.2.2, hf n⟩, hvlim,
    GradientCore.tendsto_energy_of_coe ha
      (F := fun n => smoothEnergyField hV.isOpen ha
        (isSmoothCore_of_supported ha (f n).property.1 (f n).property.2.1)) (G := H) hglim⟩


end CoarseDeGiorgi.Weighted
