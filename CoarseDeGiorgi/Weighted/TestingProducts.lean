module

public import CoarseDeGiorgi.Weighted.TestingApproximation

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

omit [NeZero d] in
/-- Multiplication by a uniformly bounded measurable scalar preserves value L¹ convergence. -/
theorem testing_tendsto_l1_mul {f : ℕ → Vec d → ℝ} {u b : Vec d → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict V))
    (hu : AEStronglyMeasurable u (volume.restrict V))
    (hb : AEStronglyMeasurable b (volume.restrict V)) {M : ℝ≥0}
    (hbound : ∀ x, |b x| ≤ M)
    (ht : Tendsto (fun n => eLpNorm (f n - u) 1 (volume.restrict V)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm ((fun x => b x * f n x) - fun x => b x * u x)
      1 (volume.restrict V)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => (M : ENNReal) * eLpNorm (f n - u) 1 (volume.restrict V))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.coe_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro n
  have h := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    ((hb.mul (hf n)).sub (hb.mul hu))
    (Eventually.of_forall fun x => show
      ‖b x * f n x - b x * u x‖₊ ≤ M * ‖f n x - u x‖₊ from
      NNReal.coe_le_coe.mp (by
        simp only [NNReal.coe_mul, coe_nnnorm, ← mul_sub, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg _))) 1
  simpa only [ENNReal.smul_def, smul_eq_mul, Pi.sub_def, Pi.mul_def] using h

omit [NeZero d] in
/-- The classical product rule in the ambient Fin-indexed gradient. -/
theorem testing_smoothGrad_mul_ae (hV : IsOpen V) {f g : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) :
    smoothGrad (fun x => f x * g x) =ᵐ[volume.restrict V]
      (fun x => f x • smoothGrad g x + g x • smoothGrad f x) := by
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  have hfd := (hf.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
  have hgd := (hg.differentiableOn (by simp) x hx).differentiableAt (hV.mem_nhds hx)
  funext i
  change fderiv ℝ (f * g) x (basisVec i) =
    f x * fderiv ℝ g x (basisVec i) + g x * fderiv ℝ f x (basisVec i)
  rw [fderiv_mul hfd hgd]
  rfl

/-- A smooth supported cutoff times a bounded smooth scalar composition is a
literal zero-boundary pair, with the weighted product gradient. -/
theorem MemH1a.cutoff_comp (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : CoarseDeGiorgi.MemH1a a V u G) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ V)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {L M : ℝ≥0}
    (hderiv : ∀ t, |deriv Φ t| ≤ L) (hbound : ∀ t, |Φ t| ≤ M) :
    MemH1a0 a V (fun x => φ x * Φ (u x))
      (fun x => φ x • (deriv Φ (u x) • G x) + Φ (u x) • smoothGrad φ x) := by
  have hφcore := isSmoothCore_of_supported ha hφ hc
  have hφM := hφ.continuous.aestronglyMeasurable (μ := volume.restrict V)
  have hφGM := smoothGrad_aestronglyMeasurable hV.isOpen hφ.contDiffOn
  obtain ⟨C, hC⟩ := hφ.continuous.norm.bddAbove_range_of_hasCompactSupport
    (hc.comp_left norm_zero)
  let B : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hφbound (x : Vec d) : |φ x| ≤ B :=
    (show ‖φ x‖ ≤ C from hC (Set.mem_range_self x)).trans (le_max_left _ _)
  have hvalM := hΦ.continuous.comp_aestronglyMeasurable hu.1
  have hi : IntegrableOn (fun x => φ x * Φ (u x)) V :=
    hφcore.2.1.mul_bdd hvalM (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hbound (u x))
  have hGout : AEStronglyMeasurable
      (fun x => φ x • (deriv Φ (u x) • G x) + Φ (u x) • smoothGrad φ x)
      (volume.restrict V) :=
    (hφM.smul ((hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable hu.1 |>.smul hu.2.1)).add
      (hvalM.smul hφGM)
  obtain ⟨huM, hG, f, hf, hcauchy, hloc, hE⟩ := hu
  have hL := (core_tendsto_l1 hV hne ha hf hcauchy huM hloc).2
  have hEG := MemH1a.energy_lt_top hV.isOpen ha
    (show CoarseDeGiorgi.MemH1a a V u G from ⟨huM, hG, f, hf, hcauchy, hloc, hE⟩)
  have hl : LipschitzWith L Φ := lipschitzWith_of_nnnorm_deriv_le (C := L)
    (hΦ.differentiable (by simp)) (fun t => NNReal.coe_le_coe.mp
      (by simpa only [coe_nnnorm, Real.norm_eq_abs] using hderiv t))
  let p : ℕ → Vec d → ℝ := fun n x => φ x * Φ (f n x)
  have hp (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (p n) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport φ
    · exact hφ.contDiffAt.mul (hΦ.contDiffAt.comp x
        ((hf n).1.contDiffAt (hV.isOpen.mem_nhds (hs hx))))
    · have hz : p n =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hx)] with y hy
        change φ y * Φ (f n y) = 0
        change φ y = 0 at hy
        rw [hy, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have hp_support (n : ℕ) : HasCompactSupport (p n) := hc.mul_right
  have hp_subset (n : ℕ) : tsupport (p n) ⊆ V :=
    (tsupport_mul_subset_left (f := φ) (g := fun x => Φ (f n x))).trans hs
  apply memH1a0_of_supported_tendsto hV ha (fun n => ⟨hp n, hp_support n, hp_subset n⟩) hi hGout
    (testing_tendsto_l1_mul
      (fun n => hΦ.continuous.comp_aestronglyMeasurable (hf n).2.1.1) hvalM hφM hφbound
      (tendsto_l1_lipschitz_comp (fun n => (hf n).2.1.1) huM hL hl))
  have hfirst := tendsto_energy_continuous_factor ha
    (f := f) (F := fun n => smoothGrad (f n)) (u := u) (G := G) (b := deriv Φ)
    (fun n => (hf n).2.1.1) huM
    (fun n => smoothGrad_aestronglyMeasurable hV.isOpen (hf n).1) hG hEG hL hE
    (hΦ.continuous_deriv (by simp)) hderiv
  have hfirstφ := tendsto_energy_bounded_mul ha
    (b := fun _ => φ) (fun _ => Eventually.of_forall hφbound) hfirst
  have hsecond := tendsto_energy_continuous_factor ha
    (f := f) (F := fun _ => smoothGrad φ) (u := u) (G := smoothGrad φ) (b := Φ)
    (fun n => (hf n).2.1.1) huM (fun _ => hφGM) hφGM hφcore.2.2 hL
    (by simp only [sub_self]; simp [weightedEnergy, CoarseDeGiorgi.weightedEnergy, vecDot, matVecMul])
    hΦ.continuous hbound
  have hsum := tendsto_energy_add_zero ha
    (F := fun n x => φ x • (deriv Φ (f n x) • smoothGrad (f n) x - deriv Φ (u x) • G x))
    (H := fun n x => Φ (f n x) • smoothGrad φ x - Φ (u x) • smoothGrad φ x)
    (fun n => hφM.smul
      (((hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable (hf n).2.1.1 |>.smul
        (smoothGrad_aestronglyMeasurable hV.isOpen (hf n).1)).sub
      ((hΦ.continuous_deriv (by simp)).comp_aestronglyMeasurable huM |>.smul hG))) hfirstφ hsecond
  convert hsum using 1
  funext n
  apply energy_congr_ae
  filter_upwards [testing_smoothGrad_mul_ae hV.isOpen hφ.contDiffOn (hΦ.comp_contDiffOn (hf n).1),
    smoothGrad_comp_ae hV.isOpen (hf n).1 hΦ] with x hx hy
  dsimp only [p, Function.comp_def, Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at hx hy ⊢
  rw [hx, hy]
  rw [smul_sub]
  abel


end CoarseDeGiorgi.Weighted
