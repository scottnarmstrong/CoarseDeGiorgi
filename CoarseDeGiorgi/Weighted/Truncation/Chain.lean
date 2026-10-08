import CoarseDeGiorgi.Weighted.Truncation.Closure
import Mathlib.Analysis.Calculus.MeanValue

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Lipschitz scalar compositions are integrable on a bounded domain. -/
theorem integrableOn_lipschitz_comp (hV : IsOpenBoundedConvexDomain V)
    {u : Vec d → ℝ} (hu : IntegrableOn u V) {Φ : ℝ → ℝ} {L : ℝ≥0}
    (hΦ : LipschitzWith L Φ) : IntegrableOn (Φ ∘ u) V := by
  let : IsFiniteMeasure (volume.restrict V) := hV.isFiniteMeasure_restrict_volume
  refine ((hu.norm.const_mul (L : ℝ)).add (integrable_const ‖Φ 0‖)).mono'
    (hΦ.continuous.comp_aestronglyMeasurable hu.1) ?_
  filter_upwards with x
  have hh := hΦ.norm_sub_le (u x) 0
  have ht := norm_add_le (Φ (u x) - Φ 0) (Φ 0)
  simpa only [Function.comp_apply, sub_zero, sub_add_cancel, Pi.add_apply] using
    ht.trans (add_le_add hh le_rfl)

/-- Lipschitz scalar composition preserves value L¹ convergence. -/
theorem tendsto_l1_lipschitz_comp {f : ℕ → Vec d → ℝ} {u : Vec d → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict V))
    (hu : AEStronglyMeasurable u (volume.restrict V))
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    {Φ : ℝ → ℝ} {L : ℝ≥0} (hΦ : LipschitzWith L Φ) :
    Tendsto (fun n => eLpNorm (Φ ∘ f n - Φ ∘ u) 1 (volume.restrict V)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n => (L : ENNReal) * eLpNorm (f n - u) 1 (volume.restrict V))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.coe_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
  intro n
  have hh := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    ((hΦ.continuous.comp_aestronglyMeasurable (hf n)).sub
      (hΦ.continuous.comp_aestronglyMeasurable hu))
    (Eventually.of_forall fun x => show ‖Φ (f n x) - Φ (u x)‖₊ ≤ L * ‖f n x - u x‖₊ from
      NNReal.coe_le_coe.mp (by simpa only [NNReal.coe_mul, coe_nnnorm] using
        (hΦ.norm_sub_le (f n x) (u x)))) 1
  simpa only [ENNReal.smul_def, smul_eq_mul, Pi.sub_def, Function.comp_def] using hh

/-- Bounded multipliers times an energy-null sequence remain energy-null. -/
theorem tendsto_energy_bounded_mul (ha : IsWeightedCoeffOn V a)
    {F : ℕ → Vec d → Vec d} {b : ℕ → Vec d → ℝ} {M : ℝ}
    (hb : ∀ n, ∀ᵐ x ∂volume.restrict V, |b n x| ≤ M)
    (ht : Tendsto (fun n => weightedEnergy a V (F n)) atTop (𝓝 0)) :
    Tendsto (fun n => weightedEnergy a V (fun x => b n x • F n x)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ENNReal.ofReal (M ^ 2) * weightedEnergy a V (F n))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => bot_le) (fun n => energy_mul_le ha (hb n))

/-- The classical gradient formula for smooth scalar composition on an open set. -/
theorem smoothGrad_comp_ae (hV : IsOpen V) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    smoothGrad (Φ ∘ f) =ᵐ[volume.restrict V]
      (fun x => deriv Φ (f x) • smoothGrad f x) := by
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  have hd := ((hΦ.differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt x
    ((hf.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
  funext i
  change fderiv ℝ (Φ ∘ f) x (basisVec i) = deriv Φ (f x) * fderiv ℝ f x (basisVec i)
  rw [hd.fderiv]
  rfl

/-- Smooth composition preserves the smooth core. -/
theorem IsSmoothCore.comp (hV : IsOpenBoundedConvexDomain V) (ha : IsWeightedCoeffOn V a)
    {f : Vec d → ℝ} (hf : CoarseDeGiorgi.IsSmoothCore a V f)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {L : ℝ≥0}
    (hbound : ∀ t, |deriv Φ t| ≤ L) : CoarseDeGiorgi.IsSmoothCore a V (Φ ∘ f) := by
  have hl : LipschitzWith L Φ := lipschitzWith_of_nnnorm_deriv_le (C := L)
    (hΦ.differentiable (by simp)) (fun t => NNReal.coe_le_coe.mp
      (by simpa only [coe_nnnorm, Real.norm_eq_abs] using hbound t))
  refine ⟨hΦ.comp_contDiffOn hf.1, integrableOn_lipschitz_comp hV hf.2.1 hl, ?_⟩
  change weightedEnergy a V (smoothGrad (Φ ∘ f)) < ⊤
  rw [energy_congr_ae (smoothGrad_comp_ae hV.isOpen hf.1 hΦ)]
  exact (energy_mul_le ha (Eventually.of_forall fun x => hbound (f x))).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2.2)

/-- Continuous bounded factors preserve convergence of value-gradient pairs. -/
theorem tendsto_energy_continuous_factor (ha : IsWeightedCoeffOn V a)
    {f : ℕ → Vec d → ℝ} {u : Vec d → ℝ} {F : ℕ → Vec d → Vec d} {G : Vec d → Vec d}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict V))
    (hu : AEStronglyMeasurable u (volume.restrict V))
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (hG : AEStronglyMeasurable G (volume.restrict V)) (hEG : weightedEnergy a V G < ⊤)
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0))
    (hE : Tendsto (fun n => weightedEnergy a V (F n - G)) atTop (𝓝 0))
    {b : ℝ → ℝ} (hb : Continuous b) {M : ℝ} (hbound : ∀ t, |b t| ≤ M) :
    Tendsto (fun n => weightedEnergy a V
      ((fun x => b (f n x) • F n x) - (fun x => b (u x) • G x))) atTop (𝓝 0) := by
  have hfirst := tendsto_energy_bounded_mul ha
    (F := fun n => F n - G) (b := fun n x => b (f n x))
    (fun n => Eventually.of_forall fun x => hbound (f n x)) hE
  have hsecond : Tendsto (fun n => weightedEnergy a V
      (fun x => (b (f n x) - b (u x)) • G x)) atTop (𝓝 0) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (ht.comp hns)).exists_seq_tendsto_ae
    refine ⟨ms, tendsto_energy_mul_zero ha hG hEG
      (fun n => (hb.comp_aestronglyMeasurable (hf (ns (ms n)))).sub
        (hb.comp_aestronglyMeasurable hu)) (M := 2 * M) ?_ ?_⟩
    · intro n
      filter_upwards with x
      exact (abs_sub _ _).trans (by linarith only [hbound (f (ns (ms n)) x), hbound (u x)])
    · filter_upwards [hae] with x hx
      simpa using (hb.continuousAt.tendsto.comp hx).sub_const (b (u x))
  have hsum := tendsto_energy_add_zero ha
    (fun n => (hb.comp_aestronglyMeasurable (hf n)).smul ((hF n).sub hG)) hfirst hsecond
  convert hsum using 1
  funext n
  congr 1
  funext x i
  change b (f n x) * F n x i - b (u x) * G x i =
    b (f n x) * (F n x i - G x i) + (b (f n x) - b (u x)) * G x i
  ring

/-- The smooth chain rule in the weighted completion (`i.weighted.chain`). -/
theorem MemH1a.comp [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {L : ℝ≥0} (hbound : ∀ t, |deriv Φ t| ≤ L) :
    CoarseDeGiorgi.MemH1a a V (Φ ∘ u) (fun x => deriv Φ (u x) • G x) := by
  have hi := (memH1a_memW11 hV hne ha hu).1
  have hEG := MemH1a.energy_lt_top hV.isOpen ha hu
  have hl : LipschitzWith L Φ := lipschitzWith_of_nnnorm_deriv_le (C := L)
    (hΦ.differentiable (by simp)) (fun t => NNReal.coe_le_coe.mp
      (by simpa only [coe_nnnorm, Real.norm_eq_abs] using hbound t))
  obtain ⟨huM, hG, f, hf, hc, hloc, hE⟩ := hu
  have hL := (core_tendsto_l1 hV hne ha hf hc huM hloc).2
  have hd : Continuous (deriv Φ) := hΦ.continuous_deriv (by simp)
  apply memH1a_of_core_tendsto hV ha (fun n => IsSmoothCore.comp hV ha (hf n) hΦ hbound)
    (integrableOn_lipschitz_comp hV hi hl) (hd.comp_aestronglyMeasurable huM |>.smul hG)
    (tendsto_l1_lipschitz_comp (fun n => (hf n).2.1.1) huM hL hl)
  have htE := tendsto_energy_continuous_factor ha (fun n => (hf n).2.1.1) huM
    (fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hf n).1) hG hEG hL hE hd hbound
  convert htE using 1
  funext n
  exact energy_congr_ae ((smoothGrad_comp_ae hV.isOpen (hf n).1 hΦ).sub EventuallyEq.rfl)

end CoarseDeGiorgi.Weighted
