module

public import CoarseDeGiorgi.Weighted.LowerResponseHilbert
public import CoarseDeGiorgi.Weighted.HarmonicCore

/-! Literal Riesz identities, harmonic attainment and square completion. -/

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators

variable {d : ℕ} [NeZero d] {V : Set (Vec d)} {a : CoeffField d}

/-- The Riesz identity for every literal weighted Sobolev pair. -/
theorem lowerRiesz_pair (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) :
    inner ℝ (memH1aEnergyField hV.isOpen ha hw : GradientHilbert ha)
      (lowerRiesz hV.isOpen ha e).val.snd = ∫ x in V, vecDot e (G x) := by
  let x : WeightedHilbert hV.isOpen ha :=
    ⟨WithLp.toLp 2 (volumeAverage V w,
      (memH1aEnergyField hV.isOpen ha hw : GradientHilbert ha)), hw.graph_mem hV hne ha⟩
  have hh := lowerRiesz_gradient_inner hV hne ha e x
  change inner ℝ (memH1aEnergyField hV.isOpen ha hw : GradientHilbert ha)
    (lowerRiesz hV.isOpen ha e).val.snd =
      vecDot e (lowerGradientIntegral ha (memH1aEnergyField hV.isOpen ha hw)) at hh
  rw [lowerGradientIntegral_coe] at hh
  rw [← lowerDot_apply, ← (lowerDot e).integral_comp_comm
    (GradientCore.integrable ha (memH1aEnergyField hV.isOpen ha hw))] at hh
  simpa only [lowerDot_apply, memH1aEnergyField_field] using hh

/-- The Riesz element represents a mean-zero weighted solution. -/
theorem exists_lowerRiesz_solution (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) :
    ∃ u : Vec d → ℝ,
      IsWeightedSolution a V u
        (gradientHilbertRep ha (lowerRiesz hV.isOpen ha e).val.snd).field ∧
      volumeAverage V u = 0 := by
  obtain ⟨u, hu, hm⟩ := weightedHilbert_exists_rep hV hne ha (lowerRiesz hV.isOpen ha e)
  refine ⟨u, ⟨hu, ?_⟩, hm.trans (lowerRiesz_mean_zero hV hne ha e)⟩
  intro φ hφ hc hs
  have ht := memH1a0_of_supported hV.isOpen ha hφ hc hs
  let F := memH1aEnergyField hV.isOpen ha (ht.memH1a ha)
  refine ⟨(pairing_integrable_and_bound ha ht.2.1 hu.2.1
    ((ht.memH1a ha).energy_lt_top hV.isOpen ha) (hu.energy_lt_top hV.isOpen ha)).1, ?_⟩
  have hh := lowerRiesz_pair hV hne ha e (ht.memH1a ha)
  rw [← gradientHilbertRep_coe ha (lowerRiesz hV.isOpen ha e).val.snd,
    gradientHilbert_inner_coe] at hh
  have hFi : IntegrableOn (smoothGrad φ) V := GradientCore.integrable ha F
  have hz : (∫ x in V, vecDot e (smoothGrad φ x)) = 0 := by
    simp_rw [← lowerDot_apply]
    rw [(lowerDot e).integral_comp_comm hFi]
    have hzero : (∫ x in V, smoothGrad φ x) = 0 := by
      funext i
      have hp := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).integral_comp_comm hFi
      exact hp.symm.trans (integral_smoothGrad_eq_zero hφ hc hs i)
    rw [hzero, map_zero]
  exact hh.trans hz

/-- The literal averaged lower integrand equals the Hilbert square-completion expression. -/
theorem lower_integrand_eq (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) :
    volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) + 2 * vecDot e (G x)) =
      (volume V).toReal⁻¹ *
        (‖(lowerRiesz hV.isOpen ha e).val.snd‖ ^ 2 -
          ‖(memH1aEnergyField hV.isOpen ha hw : GradientHilbert ha) -
            (lowerRiesz hV.isOpen ha e).val.snd‖ ^ 2) := by
  let F := memH1aEnergyField hV.isOpen ha hw
  have hdot : IntegrableOn (fun x => vecDot e (G x)) V := by
    simpa only [IntegrableOn, Function.comp_def, lowerDot_apply, F, memH1aEnergyField_field] using
      (lowerDot e).integrable_comp (GradientCore.integrable ha F)
  have hq : IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x))) V :=
    GradientCore.quadratic_integrable ha F
  unfold volumeAverage
  dsimp only
  rw [integral_add (f := fun x => -vecDot (G x) (matVecMul (a x) (G x)))
    (g := fun x => 2 * vecDot e (G x)) hq.neg (hdot.const_mul 2),
    integral_neg, integral_const_mul]
  have hnorm : ‖(memH1aEnergyField hV.isOpen ha hw : GradientHilbert ha)‖ ^ 2 =
      (weightedEnergy a V G).toReal := by
    rw [UniformSpace.Completion.norm_coe, GradientCore.norm_sq]
    rfl
  rw [← energy_toReal ha hw.2.1, ← hnorm,
    ← lowerRiesz_pair hV hne ha e hw, norm_sub_sq_real]
  ring

/-- Every weighted competitor is bounded by the Riesz energy. -/
theorem lower_integrand_le (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) (e : Vec d) {w : Vec d → ℝ} {G : Vec d → Vec d}
    (hw : MemH1a a V w G) :
    volumeAverage V (fun x => -vecDot (G x) (matVecMul (a x) (G x)) + 2 * vecDot e (G x)) ≤
      (volume V).toReal⁻¹ * ‖(lowerRiesz hV.isOpen ha e).val.snd‖ ^ 2 := by
  rw [lower_integrand_eq hV hne ha e hw]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (sq_nonneg _))
    (inv_nonneg.mpr ENNReal.toReal_nonneg)


end CoarseDeGiorgi.Weighted
