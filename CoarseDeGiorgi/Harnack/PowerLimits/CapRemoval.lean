module

public import CoarseDeGiorgi.Harnack.Selection.Cap
public import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
public import CoarseDeGiorgi.Assembly.LocalBoundedness
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

@[expose] public section

namespace CoarseDeGiorgi.Harnack.PowerLimits

open Homogenization MeasureTheory Filter Topology
open Set
open scoped ENNReal

/-- On the positive locus every sufficiently high finite cap has the original
gradient; on the zero locus locality makes the target gradient vanish.
-/
theorem positive_cap_gradient_tendsto_of_nonnegative
    {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a a (originCube 1) v G)
    (hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ v x) :
    ∀ᵐ x ∂volume.restrict (originCube 1), Tendsto
      (fun N : ℕ => Selection.selectionCapGradient 0
        ((N + 1 : ℕ) : ℝ≥0∞) v G x) atTop (𝓝 (G x)) := by
  obtain ⟨hV, hne⟩ := Assembly.theoremA_unitCube_domain d
  have hzero := Weighted.MemH1a.gradient_zero_on_level hV hne ha hv 0
  filter_upwards [hnonneg, hzero] with x hxnonneg hxzero
  by_cases hxpos : 0 < v x
  · obtain ⟨n₀, hn₀⟩ := exists_nat_gt (v x)
    have hevent : ∀ᶠ N : ℕ in atTop,
        Selection.selectionCapGradient 0 ((N + 1 : ℕ) : ℝ≥0∞) v G x = G x := by
      filter_upwards [eventually_ge_atTop n₀] with N hN
      have hcap : (((N + 1 : ℕ) : ℝ≥0∞)).toReal = (N + 1 : ℝ) := by
        rw [ENNReal.toReal_natCast]
        rw [Nat.cast_add, Nat.cast_one]
      have hfinite : ((N + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hnle : (n₀ : ℝ) ≤ (N + 1 : ℝ) := by
        exact_mod_cast Nat.le_trans hN (Nat.le_succ N)
      have hlt : v x < (((N + 1 : ℕ) : ℝ≥0∞)).toReal := by
        rw [hcap]
        exact lt_of_lt_of_le hn₀ hnle
      have hmem : x ∈ {y | 0 < v y ∧ v y < 0 +
          (((N + 1 : ℕ) : ℝ≥0∞)).toReal} := by
        simp only [Set.mem_ofPred_eq]
        exact ⟨hxpos, by simpa only [zero_add] using hlt⟩
      change (if ((N + 1 : ℕ) : ℝ≥0∞) = ⊤ then
        {y | 0 < v y}.indicator G x else
        {y | 0 < v y ∧ v y < 0 + ((N + 1 : ℕ) : ℝ≥0∞).toReal}.indicator G x) = G x
      rw [ite_eq_right hfinite]
      exact Set.indicator_of_mem hmem G
    exact (tendsto_congr' hevent).2 tendsto_const_nhds
  · have hxv : v x = 0 := le_antisymm (le_of_not_gt hxpos) hxnonneg
    have hxG : G x = 0 := by
      simpa [hxv] using hxzero
    have hevent : ∀ᶠ N : ℕ in atTop,
        Selection.selectionCapGradient 0 ((N + 1 : ℕ) : ℝ≥0∞) v G x = G x := by
      filter_upwards with N
      have hfinite : ((N + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      change (if ((N + 1 : ℕ) : ℝ≥0∞) = ⊤ then
        {y | 0 < v y}.indicator G x else
        {y | 0 < v y ∧ v y < 0 + ((N + 1 : ℕ) : ℝ≥0∞).toReal}.indicator G x) = G x
      rw [ite_eq_right hfinite]
      have hnot : x ∉ {y | 0 < v y ∧
          v y < 0 + ((N + 1 : ℕ) : ℝ≥0∞).toReal} := by
        intro hx
        have hx' : 0 < v x := hx.1
        rw [hxv] at hx'
        exact (lt_irrefl 0 hx')
      rw [Set.indicator_of_notMem hnot]
      exact hxG.symm
    exact (tendsto_congr' hevent).2 tendsto_const_nhds

/-- Dominated convergence removes the finite positive cap on every measurable
subset of the source unit cube. In particular, this gives convergence of the
interior-cube energies used in the power Caccioppoli proof.
-/
theorem positive_cap_energy_tendsto_on_subset
    {d : ℕ} [NeZero d] (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a)
    {v : Vec d → ℝ} {G : Vec d → Vec d}
    (hv : MemH1a a (originCube 1) v G)
    (hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ v x)
    {V : Set (Vec d)} (hV : V ⊆ originCube 1) :
    Tendsto (fun N : ℕ => weightedEnergy a V
      (Selection.selectionCapGradient 0 ((N + 1 : ℕ) : ℝ≥0∞) v G)) atTop
      (𝓝 (weightedEnergy a V G)) := by
  let μ : Measure (Vec d) := volume.restrict V
  let μ₁ : Measure (Vec d) := volume.restrict (originCube 1)
  let Gcap : ℕ → Vec d → Vec d := fun N =>
    Selection.selectionCapGradient 0 ((N + 1 : ℕ) : ℝ≥0∞) v G
  let F : Vec d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))
  let Fcap : ℕ → Vec d → ℝ≥0∞ := fun N x =>
    ENNReal.ofReal (vecDot (Gcap N x) (matVecMul (a x) (Gcap N x)))
  have hμ : μ ≤ μ₁ := Measure.restrict_mono hV le_rfl
  have hGlim₁ := positive_cap_gradient_tendsto_of_nonnegative a ha hv hnonneg
  have hGlim : ∀ᵐ x ∂μ, Tendsto (fun N => Gcap N x) atTop (𝓝 (G x)) :=
    ae_mono hμ hGlim₁
  have hGmeas : AEStronglyMeasurable G μ₁ := hv.2.1
  have hFmeas₁ : AEMeasurable F μ₁ := by
    apply (ENNReal.continuous_ofReal.comp_aestronglyMeasurable ?_).aemeasurable
    exact Weighted.quadratic_aestronglyMeasurable ha hGmeas
  have hFmeas : AEMeasurable F μ := hFmeas₁.mono_measure hμ
  have hcapmeas (N : ℕ) : AEStronglyMeasurable (Gcap N) μ₁ := by
    have hN : ((N + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
    exact (Selection.selectionCap_memH1a a ha hv 0 _ hN).2.1
  have hFcapmeas (N : ℕ) : AEMeasurable (Fcap N) μ := by
    apply (ENNReal.continuous_ofReal.comp_aestronglyMeasurable ?_).aemeasurable
    exact (Weighted.quadratic_aestronglyMeasurable ha (hcapmeas N)).mono_measure hμ
  have hFfin₁ : (∫⁻ x, F x ∂μ₁) < ⊤ := by
    simpa only [F, μ₁, weightedEnergy, CoarseDeGiorgi.weightedEnergy] using
      (Weighted.MemH1a.energy_lt_top (Assembly.caccioppoli_cube_open 1) ha hv)
  have hFfin : (∫⁻ x, F x ∂μ) < ⊤ := by
    apply (lintegral_mono' hμ (fun _ => le_rfl)).trans_lt hFfin₁
  have hdom (N : ℕ) : ∀ᵐ x ∂μ, Fcap N x ≤ F x := by
    filter_upwards with x
    exact Selection.selectionCap_density_le a v G 0 ((N + 1 : ℕ) : ℝ≥0∞) x
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun N => Fcap N x) atTop (𝓝 (F x)) := by
    filter_upwards [hGlim] with x hx
    have hquad : Continuous (fun z : Vec d =>
        ENNReal.ofReal (vecDot z (matVecMul (a x) z))) := by
      apply ENNReal.continuous_ofReal.comp
      unfold vecDot matVecMul
      fun_prop
    have h := hquad.continuousAt.tendsto.comp hx
    simpa only [Fcap, F, Gcap, Function.comp_def] using h
  have hlim := tendsto_lintegral_of_dominated_convergence' F hFcapmeas hdom hFfin.ne hpoint
  simpa only [Fcap, F, Gcap, μ, weightedEnergy, CoarseDeGiorgi.weightedEnergy] using hlim

end CoarseDeGiorgi.Harnack.PowerLimits
