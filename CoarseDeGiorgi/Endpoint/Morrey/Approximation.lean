module

public import CoarseDeGiorgi.Endpoint.Morrey.Smooth
public import Homogenization.Sobolev.W1p.H1GradientUpgrade
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Passage of Morrey estimates to weak representatives -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint.Morrey

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

/-- Finite-exponent convergence on a finite measure space controls the mean. -/
theorem tendsto_integral_of_tendsto_eLpNorm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, MemLp (f n) p μ)
    (hg : MemLp g p μ)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (nhds (∫ x, g x ∂μ)) := by
  let K : ℝ≥0∞ := μ Set.univ ^ (1 - 1 / p.toReal)
  have hpow : 0 ≤ 1 - 1 / p.toReal := by
    by_cases hptop : p = ⊤
    · simp [hptop]
    · have hpReal : (1 : ℝ) ≤ p.toReal := by
        simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hptop hp
      exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hpReal)).mpr hpReal)
  have hK : K ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg hpow (measure_ne_top μ _)).ne
  have hbound (n : ℕ) : eLpNorm (f n - g) 1 μ ≤ eLpNorm (f n - g) p μ * K := by
    simpa only [ENNReal.toReal_one, div_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp ((hf n).sub hg).aestronglyMeasurable
  have hscaled : Tendsto (fun n => eLpNorm (f n - g) p μ * K) atTop (nhds 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hconv (Or.inr hK)
  have hL1 := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled
    (fun _ => zero_le) hbound
  exact tendsto_integral_of_L1' (f := g)
    (Eventually.of_forall fun n => (hf n).integrable hp) hL1

/-- Fatou's inequality with a convergent, varying sequence of norm bounds. -/
theorem eLpNorm_le_of_tendstoInMeasure_bound {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : ℕ → α → E} {g : α → E}
    {p : ℝ≥0∞} {B : ℕ → ℝ≥0∞} {b : ℝ≥0∞}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hconv : TendstoInMeasure μ f atTop g) (hB : Tendsto B atTop (nhds b))
    (hbound : ∀ n, eLpNorm (f n) p μ ≤ B n) : eLpNorm g p μ ≤ b := by
  obtain ⟨l, hl, hae⟩ := hconv.exists_seq_tendsto_ae'
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p) (fun n => hf (l n)) g hg hae
  refine hfatou.trans ?_
  calc
    atTop.liminf (fun n => eLpNorm (f (l n)) p μ) ≤ atTop.liminf (fun n => B (l n)) :=
      liminf_le_liminf (Eventually.of_forall fun n => hbound (l n))
    _ = b := (hB.comp hl).liminf_eq

/-- The smooth Morrey bound extends to every `W^{1,p}` representative.
The domain is fixed here; the cube dilation is handled separately. -/
theorem exists_weak_morrey_bound {d : ℕ} [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    {p s : ℝ} (hps : p.HolderConjugate s) (hds : ((d : ℝ) - 1) * s < d)
    (R : ℝ) (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖y - x‖ < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1pFunction U (ENNReal.ofReal p),
      eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) ⊤ (volume.restrict U) ≤
        ENNReal.ofReal (C * u.gradientCoordLpSeminormSum) := by
  classical
  let μ := volume.restrict U
  let : IsFiniteMeasure μ := hU.isFiniteMeasure_restrict_volume
  have hp : 1 ≤ ENNReal.ofReal p := by rw [ENNReal.one_le_ofReal]; exact hps.lt.le
  obtain ⟨C, hC, hCsmooth⟩ := exists_smooth_morrey_bound hU hne hps hds R hdiam
  refine ⟨C, hC, ?_⟩
  intro u
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU.isOpen x0 hx0
  have hr2 : 0 < r / 2 := half_pos hr
  have hclosed : Metric.closedBall x0 (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  let ψ : ℕ → W1pFunction U (ENNReal.ofReal p) :=
    W1pFunction.convexApproxSmoothW1p hU hp u x0 hr2
  have hval : Tendsto (fun n => eLpNorm ((ψ n).toFun - u.toFun) (ENNReal.ofReal p) μ)
      atTop (nhds 0) :=
    W1pFunction.tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
      hU hp ENNReal.ofReal_ne_top u hclosed hr2
  have havg : Tendsto (fun n => integralAverage U (ψ n).toFun) atTop
      (nhds (integralAverage U u.toFun)) := by
    unfold integralAverage
    exact tendsto_const_nhds.mul (tendsto_integral_of_tendsto_eLpNorm hp
      (fun n => (ψ n).memLp) u.memLp hval)
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm
    (ENNReal.ofReal_pos.mpr hps.pos).ne' hval
  obtain ⟨l, hl, hae⟩ := hmeas.exists_seq_tendsto_ae'
  have hcenter : ∀ᵐ x ∂μ, Tendsto
      (fun n => (ψ (l n)).toFun x - integralAverage U (ψ (l n)).toFun) atTop
      (nhds (u.toFun x - integralAverage U u.toFun)) := by
    filter_upwards [hae] with x hx
    exact hx.sub (havg.comp hl)
  have hnorm (n : ℕ) :
      eLpNorm (fun x => (ψ n).toFun x - integralAverage U (ψ n).toFun) ⊤ μ ≤
        ENNReal.ofReal (C * (ψ n).gradientCoordLpSeminormSum) := by
    let f := convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d))
      u.toFun x0 (r / 2) (unitConvexApproxScale n)
    have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
      contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
        (isConvexApproxKernel_unitConvexApproxKernel (d := d)) hp u.memLp hr2
        (W1pFunction.unitConvexApproxScale_pos n)
    have hψ : ψ n = W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
        (hf.of_le (by simp)) := rfl
    have hfun : (ψ n).toFun = f := rfl
    have hfd : MemLp (fderiv ℝ f) (ENNReal.ofReal p) μ :=
      W1pFunction.memLp_fderiv_of_contDiffOnIsOpenBoundedConvexDomain
        hU (hf.of_le (by simp))
    have hb := hCsmooth f hf hfd.norm
    rw [eLpNorm_norm _ hfd.aestronglyMeasurable] at hb
    have hcoords := W1pFunction.fderivLpNorm_le_gradientCoordLpSeminormSum_ofContDiffOnIsOpenBoundedConvexDomain
      hU hp hf
    rw [← hψ] at hcoords
    rw [hfun]
    refine hb.trans ?_
    rw [← ENNReal.ofReal_toReal hfd.eLpNorm_ne_top, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcoords hC)
  have hgrad := W1pFunction.tendsto_convexApproxSmoothW1p_gradientCoordLpSeminormSum
    hU hp ENNReal.ofReal_ne_top u hclosed hr2
  have hB : Tendsto (fun n => ENNReal.ofReal (C * (ψ (l n)).gradientCoordLpSeminormSum))
      atTop (nhds (ENNReal.ofReal (C * u.gradientCoordLpSeminormSum))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (hgrad.comp hl))
  have hfmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => (ψ (l n)).toFun x - integralAverage U (ψ (l n)).toFun) μ :=
    (ψ (l n)).memLp.aestronglyMeasurable.sub aestronglyMeasurable_const
  exact eLpNorm_le_of_tendstoInMeasure_bound hfmeas
    (u.memLp.aestronglyMeasurable.sub aestronglyMeasurable_const)
    (tendstoInMeasure_of_tendsto_ae hfmeas hcenter) hB (fun n => hnorm (l n))

end

end CoarseDeGiorgi.Endpoint.Morrey
