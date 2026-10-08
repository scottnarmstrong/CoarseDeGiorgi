import CoarseDeGiorgi.Foundations.Reconstruction.PeriodicMeasure
import CoarseDeGiorgi.Foundations.Reconstruction.AssemblyBlocks
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Translation continuity in the ordinary periodic `L^r` space -/

namespace CoarseDeGiorgi.Foundations.Reconstruction

open Homogenization MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section
variable {d : ℕ}

/-- Bounded a.e. convergence on a finite measure space implies convergence of
finite-exponent norms. This also applies to the translation filter. -/
theorem smoothing_eLpNorm_tendsto_zero {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {l : Filter I} [l.IsCountablyGenerated]
    {f : I → X → ℝ} {r B : ℝ} (hr : 0 < r)
    (hf : ∀ i, Measurable (f i))
    (hb : ∀ i x, ‖f i x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) (ENNReal.ofReal r) μ) l (𝓝 0) := by
  have hi := tendsto_lintegral_filter_of_dominated_convergence
    (μ := μ) (fun _ => ENNReal.ofReal B ^ r)
    (Eventually.of_forall fun i => ((hf i).enorm.pow_const r))
    (Eventually.of_forall fun i => ae_of_all _ fun x =>
      ENNReal.rpow_le_rpow (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hb i x)) hr.le)
    (by simp only [lintegral_const]; finiteness)
    (hlim.mono fun x hx => by
      simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hr] using
        (hx.enorm.ennrpow_const r))
  simp only [lintegral_zero] at hi
  have ht := hi.ennrpow_const (1 / r)
  simp only [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr)] at ht
  convert ht using 1
  ext i
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ne_of_gt (ENNReal.ofReal_pos.mpr hr))
    ENNReal.ofReal_ne_top (hf i).aestronglyMeasurable, ENNReal.toReal_ofReal hr.le]

/-- Wrapping is locally the identity at every interior point of the fundamental box. -/
theorem smoothing_wrapBox_tendsto (m : ℤ) {x : Vec d} (hx : x ∈ reflectionBox m) :
    Tendsto (fun u : Vec d => wrapBox m (x + u)) (𝓝 0) (𝓝 x) := by
  have ht : Tendsto (fun u : Vec d => x + u) (𝓝 0) (𝓝 x) := by
    simpa only [id_eq, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Vec d => x) (𝓝 0) (𝓝 x)).add
        (tendsto_id : Tendsto (fun u : Vec d => u) (𝓝 0) (𝓝 0))
  have hopen : IsOpen (reflectionBox (d := d) m) := by
    simp only [reflectionBox, ← Set.iInter_ofPred]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).abs continuous_const
  apply ht.congr'
  filter_upwards [ht.eventually (hopen.mem_nhds hx)] with u hu
  exact (wrapBox_eq_self m hu).symm

/-- Bounded continuous approximants need no boundary matching: the wrapping seams
are a null set, and dominated convergence treats the interior. -/
theorem smoothing_wrapped_continuous_translation (m : ℤ) (g : BoundedContinuousFunction (Vec d) ℝ)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun u : Vec d => eLpNorm (fun x => g (wrapBox m (x + u)) - g (wrapBox m x))
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m))) (𝓝 0) (𝓝 0) := by
  let : IsFiniteMeasure (volume.restrict (reflectionBox (d := d) m)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      apply measure_lt_top_of_subset (s := Metric.closedBall (0 : Vec d) (auxSide m))
      · intro x hx
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (pi_norm_le_iff_of_nonneg (auxSide_pos m).le).mpr fun i =>
          by simpa only [Real.norm_eq_abs] using (hx i).le
      · exact (isCompact_closedBall (0 : Vec d) (auxSide m)).measure_ne_top
    ⟩
  apply smoothing_eLpNorm_tendsto_zero _ hr
    (fun u => (g.continuous.measurable.comp ((measurable_wrapBox m).comp
      (measurable_id.add_const u))).sub (g.continuous.measurable.comp (measurable_wrapBox m)))
    (B := 2 * ‖g‖)
  · intro u x
    exact (norm_sub_le _ _).trans (add_le_add (g.norm_coe_le_norm _) (g.norm_coe_le_norm _) |>.trans_eq (by ring))
  · filter_upwards [ae_restrict_mem (assembly_reflectionBox_measurable m)] with x hx
    have ht := g.continuous.continuousAt.tendsto.comp (smoothing_wrapBox_tendsto m hx)
    simpa only [Function.comp_apply, Pi.sub_apply, id_eq, wrapBox_eq_self m hx, sub_self] using ht.sub_const (g x)


/-- Finite unnormalized volume on the periodic integration box. -/
theorem smoothing_reflectionBox_finite (m : ℤ) : volume (reflectionBox (d := d) m) < ∞ := by
  apply measure_lt_top_of_subset (s := Metric.closedBall (0 : Vec d) (auxSide m))
  · intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (auxSide_pos m).le).mpr fun i =>
      by simpa only [Real.norm_eq_abs] using (hx i).le
  · exact (isCompact_closedBall (0 : Vec d) (auxSide m)).measure_ne_top

/-- Density and invariance of the period measure give translation continuity
for every finite-exponent periodic `L^r` field, including arbitrary a.e. representatives. -/
theorem smoothing_periodic_translation (m : ℤ) {F : Vec d → ℝ} {r : ℝ} (hr : 1 < r)
    (hF : MemLp F (ENNReal.ofReal r) (volume.restrict (reflectionBox m)))
    (hp : ∀ i x, F (x + (2 * auxSide m) • basisVec i) = F x) :
    Tendsto (fun u : Vec d => eLpNorm (fun x => F (x + u) - F x)
      (ENNReal.ofReal r) (volume.restrict (reflectionBox m))) (𝓝 0) (𝓝 0) := by
  let μ := volume.restrict (reflectionBox (d := d) m)
  let : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using
    smoothing_reflectionBox_finite (d := d) m⟩
  have hp1 : 1 ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hr.le
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (3 : ℝ≥0∞)) (by norm_num) (ne_of_gt hε)
  obtain ⟨g, hg, _⟩ := hF.exists_boundedContinuous_eLpNorm_sub_le ENNReal.ofReal_ne_top
    (ne_of_gt (ENNReal.coe_pos.mpr hδ))
  let G : Vec d → ℝ := fun x => g (wrapBox m x)
  have hG : Measurable G := g.continuous.measurable.comp (measurable_wrapBox m)
  have hGp (i : Fin d) (x : Vec d) : G (x + (2 * auxSide m) • basisVec i) = G x := by
    dsimp only [G]
    rw [wrapBox_add_period_basisVec]
  have hGeq : G =ᵐ[μ] g := by
    filter_upwards [ae_restrict_mem (assembly_reflectionBox_measurable m)] with x hx
    dsimp only [G]
    rw [wrapBox_eq_self m hx]
  have herr : eLpNorm (F - G) (ENNReal.ofReal r) μ ≤ δ := by
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ F) hGeq)]
    exact hg
  have hsmall := ENNReal.tendsto_nhds_zero.mp
    (smoothing_wrapped_continuous_translation m g (zero_lt_one.trans hr))
    δ (ENNReal.coe_pos.mpr hδ)
  filter_upwards [hsmall] with u hu
  have hsplit : (fun x => F (x + u) - F x) =
      ((fun x => (F - G) (x + u)) + (fun x => G (x + u) - G x)) + (G - F) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  have htr := eLpNorm_periodicField_add m (F - G)
    (hF.aestronglyMeasurable.sub hG.aestronglyMeasurable)
    (fun i x => by simp only [Pi.sub_apply, hp, hGp]) u (ENNReal.ofReal r)
  calc
    _ ≤ (eLpNorm (fun x => (F - G) (x + u)) (ENNReal.ofReal r) μ +
        eLpNorm (fun x => G (x + u) - G x) (ENNReal.ofReal r) μ) +
          eLpNorm (G - F) (ENNReal.ofReal r) μ :=
      (eLpNorm_add_le hp1).trans (add_le_add (eLpNorm_add_le hp1) le_rfl)
    _ ≤ ((δ : ℝ≥0∞) + δ) + δ := by
      rw [htr]
      have hrev : eLpNorm (G - F) (ENNReal.ofReal r) μ ≤ δ := by
        rw [eLpNorm_sub_comm]
        exact herr
      exact add_le_add (add_le_add herr hu) hrev
    _ ≤ ε := (le_of_eq (by ring)).trans hδε.le

end
end CoarseDeGiorgi.Foundations.Reconstruction
