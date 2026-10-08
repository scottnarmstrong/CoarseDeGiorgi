module

public import CoarseDeGiorgi.Weighted.Truncation.Closure

/-! Restriction of weighted pairs to smaller bounded convex domains. -/

@[expose] public section

namespace CoarseDeGiorgi.LowerFractional

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {a : CoeffField d} {V U : Set (Vec d)}

/-- Coefficient hypotheses restrict to subsets. -/
theorem weightedCoeffOn_mono (ha : CoarseDeGiorgi.IsWeightedCoeffOn V a) (hUV : U ⊆ V) :
    CoarseDeGiorgi.IsWeightedCoeffOn U a :=
  ⟨ha.1.mono_set hUV, ae_restrict_of_ae_restrict_of_subset hUV ha.2.1,
    ha.2.2.1.mono_set hUV, ha.2.2.2.mono_set hUV⟩

/-- Monotonicity of the extended weighted energy under domain restriction. -/
theorem weightedEnergy_mono (hUV : U ⊆ V) (G : Vec d → Vec d) :
    CoarseDeGiorgi.weightedEnergy a U G ≤ CoarseDeGiorgi.weightedEnergy a V G :=
  lintegral_mono_set hUV

/-- The same core approximants prove membership on the smaller domain.
Only the enclosing domain needs positive dimension for its existing L¹ identification. -/
theorem memH1a_restrict [NeZero d] (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (ha : CoarseDeGiorgi.IsWeightedCoeffOn V a)
    (hU : IsOpenBoundedConvexDomain U) (hUV : U ⊆ V)
    {w : Vec d → ℝ} {G : Vec d → Vec d} (hw : CoarseDeGiorgi.MemH1a a V w G) :
    CoarseDeGiorgi.MemH1a a U w G := by
  obtain ⟨hwM, hGM, f, hf, hc, hloc, hE⟩ := hw
  have hL := Weighted.core_tendsto_l1 hV hne ha hf hc hwM hloc
  have hLU : Tendsto (fun n => eLpNorm (f n - w) 1 (volume.restrict U)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL.2
      (fun _ => bot_le) (fun n => eLpNorm_mono_measure _ (Measure.restrict_mono hUV le_rfl))
  have hEU : Tendsto
      (fun n => CoarseDeGiorgi.weightedEnergy a U (Weighted.smoothGrad (f n) - G))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hE
      (fun _ => bot_le) (fun n => weightedEnergy_mono hUV _)
  exact Weighted.memH1a_of_core_tendsto hU (weightedCoeffOn_mono ha hUV)
    (fun n => ⟨(hf n).1.mono hUV, (hf n).2.1.mono_set hUV,
      (weightedEnergy_mono hUV _).trans_lt (hf n).2.2⟩)
    (hL.1.mono_set hUV) (hGM.mono_set hUV) hLU hEU


end CoarseDeGiorgi.LowerFractional
