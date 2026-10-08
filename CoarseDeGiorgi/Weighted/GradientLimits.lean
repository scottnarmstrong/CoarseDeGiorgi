module

public import CoarseDeGiorgi.Weighted.GradientHilbert
public import CoarseDeGiorgi.Weighted.L1Tools
public import CoarseDeGiorgi.Foundations.Euclid.Basic

@[expose] public section

namespace CoarseDeGiorgi.Weighted

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- Fatou's lemma for the weighted quadratic energy. -/
theorem energy_le_liminf_of_ae_tendsto (ha : IsWeightedCoeffOn V a)
    {F : ℕ → Vec d → Vec d} {G : Vec d → Vec d}
    (hF : ∀ n, AEStronglyMeasurable (F n) (volume.restrict V))
    (ht : ∀ᵐ x ∂(volume.restrict V), Tendsto (fun n => F n x) atTop (𝓝 (G x))) :
    weightedEnergy a V G ≤ liminf (fun n => weightedEnergy a V (F n)) atTop := by
  have hq : ∀ᵐ x ∂(volume.restrict V),
      liminf (fun n => ENNReal.ofReal
        (vecDot (F n x) (matVecMul (a x) (F n x)))) atTop =
          ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x))) := by
    filter_upwards [ht] with x hx
    have hcont : Continuous (fun z : Vec d =>
        ENNReal.ofReal (vecDot z (matVecMul (a x) z))) := by
      apply ENNReal.continuous_ofReal.comp
      unfold vecDot matVecMul
      fun_prop
    exact (hcont.continuousAt.tendsto.comp hx).liminf_eq
  change (∫⁻ x in V, ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) ≤ _
  rw [← lintegral_congr_ae hq]
  exact lintegral_liminf_le' fun n =>
    (quadratic_aestronglyMeasurable ha (hF n)).aemeasurable.ennreal_ofReal

namespace GradientCore

variable (ha : IsWeightedCoeffOn V a)

/-- The inverse trace estimate embeds energy representatives continuously in L¹. -/
theorem integrable (G : GradientCore ha) : Integrable G.field (volume.restrict V) := by
  have hl := gradient_length_integrable_and_bound ha (measurable ha G) (energy_lt_top ha G)
  exact Integrable.of_eval fun i => coord_integrable_of_length (measurable ha G) hl.1 i

noncomputable def toL1 : GradientCore ha →L[ℝ] Lp (Vec d) 1 (volume.restrict V) :=
  LinearMap.mkContinuous
    { toFun := fun G => (integrable ha G).toL1 G.field
      map_add' := fun G H => Integrable.toL1_add G.field H.field
        (integrable ha G) (integrable ha H)
      map_smul' := fun c G => Integrable.toL1_smul' G.field (integrable ha G) c }
    (Real.sqrt (∫ x in V, ((a x)⁻¹).trace)) (by
      intro G
      change ‖(integrable ha G).toL1 G.field‖ ≤ _
      rw [Integrable.norm_toL1_eq_lintegral_enorm,
        ← integral_norm_eq_lintegral_enorm (measurable ha G), ← Real.sqrt_sq (norm_nonneg G), norm_sq ha G]
      exact (integral_mono_ae (integrable ha G).norm
        (gradient_length_integrable_and_bound ha (measurable ha G) (energy_lt_top ha G)).1
        (Eventually.of_forall fun x => Foundations.Euclid.norm_le_eNorm2 (G.field x))).trans
          (gradient_length_integrable_and_bound ha (measurable ha G) (energy_lt_top ha G)).2)

/-- Every energy-Cauchy sequence has a measurable finite-energy representative as limit. -/
theorem exists_energy_limit {F : ℕ → GradientCore ha} (hc : CauchySeq F) :
    ∃ G : GradientCore ha,
      Tendsto (fun n => weightedEnergy a V ((F n).field - G.field)) atTop (𝓝 0) := by
  obtain ⟨W, hW⟩ := cauchySeq_tendsto_of_complete
    ((toL1 ha).uniformContinuous.comp_cauchySeq hc)
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hW).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂(volume.restrict V), ∀ n,
      (toL1 ha (F (ns n))) x = (F (ns n)).field x := by
    exact ae_all_iff.mpr fun n => (integrable ha (F (ns n))).coeFn_toL1
  have ht : ∀ᵐ x ∂(volume.restrict V),
      Tendsto (fun n => (F (ns n)).field x) atTop (𝓝 (W x)) := by
    filter_upwards [hAE, hrep] with x hx he
    simpa only [Function.comp_def, he] using hx
  have hb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      weightedEnergy a V ((F n).field - fun x => W x) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨N, fun n hn => ?_⟩
    have hfat := energy_le_liminf_of_ae_tendsto ha
      (fun k => (measurable ha (F n)).sub (measurable ha (F (ns k))))
      (ht.mono fun x hx => tendsto_const_nhds.sub hx)
    refine hfat.trans (liminf_le_of_frequently_le ?_)
    apply Eventually.frequently
    filter_upwards [hns.tendsto_atTop.eventually (eventually_ge_atTop N)] with k hk
    have hh := hN n hn (ns k) hk
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg (F n - F (ns k))), norm_sq] at hh
    have hfinite := (energy_lt_top ha (F n - F (ns k))).ne
    have hreal : (weightedEnergy a V ((F n).field - (F (ns k)).field)).toReal ≤ ε := by
      exact (Real.sqrt_le_sqrt_iff hε.le).mp hh.le
    exact (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hε.le, field_sub] using hreal)
  obtain ⟨N, hN⟩ := hb 1 zero_lt_one
  have hE : weightedEnergy a V (fun x => W x) < ⊤ := by
    have hd : weightedEnergy a V (-(F N).field + fun x => W x) < ⊤ := by
      rw [show -(F N).field + (fun x => W x) =
        -((F N).field - fun x => W x) by abel, energy_neg]
      exact (hN N le_rfl).trans_lt ENNReal.ofReal_lt_top
    have hh := energy_add_lt_top ha (measurable ha (F N))
      (((measurable ha (F N)).neg).add (Lp.aestronglyMeasurable W))
      (energy_lt_top ha (F N)) hd
    convert hh using 1
    congr 1
    abel
  let G : GradientCore ha := ⟨fun x => W x, Lp.aestronglyMeasurable W,
    CoarseDeGiorgi.Weighted.quadratic_integrable ha (Lp.aestronglyMeasurable W) hE⟩
  refine ⟨G, ?_⟩
  apply tendsto_order.2
  constructor
  · intro b hb0
    exact Eventually.of_forall fun n => hb0.trans_le bot_le
  · intro b hb0
    obtain ⟨ε, _, hε, hεb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb0
    have hεpos : 0 < ε := ENNReal.ofReal_pos.mp hε
    obtain ⟨M, hM⟩ := hb ε hεpos
    exact (eventually_ge_atTop M).mono fun n hn => (hM n hn).trans_lt hεb

end GradientCore

end CoarseDeGiorgi.Weighted
