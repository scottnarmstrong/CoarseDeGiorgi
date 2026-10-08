module

public import CoarseDeGiorgi.Weighted.GradientLimits
public import Mathlib.Topology.Sequences

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

namespace GradientCore

variable (ha : IsWeightedCoeffOn V a)

/-- The literal extended energy is the square of the energy seminorm. -/
theorem energy_eq_norm_sq (G : GradientCore ha) :
    weightedEnergy a V G.field = ENNReal.ofReal (‖G‖ ^ 2) := by
  rw [norm_sq ha G, ENNReal.ofReal_toReal (energy_lt_top ha G).ne]

/-- Energy convergence is convergence in the shared Hilbert ambient space. -/
theorem tendsto_coe_of_energy {F : ℕ → GradientCore ha} {G : GradientCore ha}
    (ht : Tendsto (fun n => weightedEnergy a V ((F n).field - G.field)) atTop (𝓝 0)) :
    Tendsto (fun n => (F n : GradientHilbert ha)) atTop (𝓝 (G : GradientHilbert ha)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr : Tendsto (fun n => (weightedEnergy a V ((F n).field - G.field)).toReal)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, Real.sqrt_zero, ← field_sub,
    ← norm_sq ha, Real.sqrt_sq (norm_nonneg _),
    ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe] using hs

/-- Hilbert convergence of represented fields implies literal energy convergence. -/
theorem tendsto_energy_of_coe {F : ℕ → GradientCore ha} {G : GradientCore ha}
    (ht : Tendsto (fun n => (F n : GradientHilbert ha)) atTop (𝓝 (G : GradientHilbert ha))) :
    Tendsto (fun n => weightedEnergy a V ((F n).field - G.field)) atTop (𝓝 0) := by
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp ht
  have hs := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hn.pow 2)
  simpa only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0),
    ENNReal.ofReal_zero, ← UniformSpace.Completion.coe_sub,
    UniformSpace.Completion.norm_coe, ← energy_eq_norm_sq ha, field_sub] using hs

/-- Passing into the completion identifies exactly a.e.-equal gradient fields. -/
theorem coe_eq_iff (G H : GradientCore ha) :
    (G : GradientHilbert ha) = (H : GradientHilbert ha) ↔
      G.field =ᵐ[volume.restrict V] H.field := by
  constructor
  · intro h
    have hnorm : ‖G - H‖ = 0 := by
      rw [← UniformSpace.Completion.norm_coe,
        UniformSpace.Completion.coe_sub, h, sub_self, norm_zero]
    have hL : toL1 ha G = toL1 ha H := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      have hb := (toL1 ha).le_opNorm (G - H)
      simpa only [map_sub, hnorm, mul_zero] using hb
    exact (Integrable.toL1_eq_toL1_iff G.field H.field (integrable ha G)
      (integrable ha H)).mp hL
  · intro h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
    apply eq_zero_of_pow_eq_zero (n := 2)
    rw [norm_sq ha, energy_toReal ha (measurable ha (G - H))]
    apply integral_eq_zero_of_ae
    filter_upwards [h] with x hx
    simp only [field_sub, Pi.sub_apply, hx, sub_self, vecDot_zero_left, Pi.zero_apply]

end GradientCore

/-- No extra abstract elements occur: every gradient completion element has a field. -/
theorem gradientHilbert_exists_rep (ha : IsWeightedCoeffOn V a) (x : GradientHilbert ha) :
    ∃ G : GradientCore ha, (G : GradientHilbert ha) = x := by
  obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp
    (UniformSpace.Completion.denseRange_coe x)
  choose F hF using hy
  have htF : Tendsto (fun n => (F n : GradientHilbert ha)) atTop (𝓝 x) := by
    simpa only [hF] using ht
  have hc : CauchySeq F :=
    (UniformSpace.Completion.isUniformInducing_coe (GradientCore ha)).cauchy_map_iff.mp
      htF.cauchySeq
  obtain ⟨G, hG⟩ := GradientCore.exists_energy_limit ha hc
  exact ⟨G, tendsto_nhds_unique (GradientCore.tendsto_coe_of_energy ha hG) htF⟩

/-- A choice of measurable finite-energy representative of a Hilbert gradient. -/
noncomputable def gradientHilbertRep (ha : IsWeightedCoeffOn V a) (x : GradientHilbert ha) :
    GradientCore ha := Classical.choose (gradientHilbert_exists_rep ha x)

theorem gradientHilbertRep_coe (ha : IsWeightedCoeffOn V a) (x : GradientHilbert ha) :
    (gradientHilbertRep ha x : GradientHilbert ha) = x :=
  Classical.choose_spec (gradientHilbert_exists_rep ha x)

end CoarseDeGiorgi.Weighted
