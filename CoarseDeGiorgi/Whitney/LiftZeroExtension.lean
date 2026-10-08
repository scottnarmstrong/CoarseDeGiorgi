module

public import CoarseDeGiorgi.Weighted.PairOperations

/-! # Zero extension of weighted zero-boundary pairs

The cell's supported smooth approximations are already global functions. They
therefore serve as ambient approximations without a new smoothing step.
-/

@[expose] public section

namespace CoarseDeGiorgi.Whitney
open Homogenization MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
variable {d : ℕ} {U V : Set (Vec d)} {a : CoeffField d}

lemma lift_coeff_mono (ha : IsWeightedCoeffOn V a) (hUV : U ⊆ V) : IsWeightedCoeffOn U a :=
  ⟨ha.1.mono_measure (Measure.restrict_mono hUV le_rfl),
    ae_mono (Measure.restrict_mono hUV le_rfl) ha.2.1,
    ha.2.2.1.mono_set hUV, ha.2.2.2.mono_set hUV⟩

/-- Extending a gradient by zero preserves its unnormalized energy exactly. -/
lemma lift_energy_indicator (hU : MeasurableSet U) (hUV : U ⊆ V) (G : Vec d → Vec d) :
    weightedEnergy a V (U.indicator G) = weightedEnergy a U G := by
  unfold weightedEnergy
  have he : (fun x => ENNReal.ofReal (vecDot (U.indicator G x)
      (matVecMul (a x) (U.indicator G x)))) =
      U.indicator (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, vecDot_zero_left, ENNReal.ofReal_zero]
  rw [he, lintegral_indicator hU, Measure.restrict_restrict hU,
    inter_eq_left.mpr hUV]

lemma lift_smoothGrad_zero_outside {φ : Vec d → ℝ} (hφ : tsupport φ ⊆ U) {x : Vec d}
    (hx : x ∉ U) : smoothGrad φ x = 0 := by
  have hz := fderiv_of_notMem_tsupport (𝕜 := ℝ) (show x ∉ tsupport φ from fun ht => hx (hφ ht))
  funext i
  simp only [smoothGrad, hz, zero_apply, Pi.zero_apply]

lemma lift_supported_eq_indicator {φ : Vec d → ℝ} (hφ : tsupport φ ⊆ U) :
    U.indicator φ = φ := by
  funext x
  by_cases hx : x ∈ U
  · exact indicator_of_mem hx φ
  · rw [indicator_of_notMem hx]
    have hz : φ x = 0 := by
      by_contra hn
      exact hx (hφ (subset_tsupport φ hn))
    exact hz.symm

lemma lift_supported_gradient_eq_indicator {φ : Vec d → ℝ} (hφ : tsupport φ ⊆ U) :
    U.indicator (smoothGrad φ) = smoothGrad φ := by
  funext x
  by_cases hx : x ∈ U
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, lift_smoothGrad_zero_outside hφ hx]

/-- A cell correction remains in the ambient weighted zero-boundary completion. -/
theorem lift_zero_extension [NeZero d] (hU : IsOpenBoundedConvexDomain U) (hneU : U.Nonempty)
    (hV : IsOpen V) (hUV : U ⊆ V) (ha : IsWeightedCoeffOn V a)
    {u : Vec d → ℝ} {G : Vec d → Vec d} (hu : MemH1a0 a U u G) :
    MemH1a0 a V (U.indicator u) (U.indicator G) := by
  have haU := lift_coeff_mono ha hUV
  have huI := (Weighted.memH1a_memW11 hU hneU haU (Weighted.MemH1a0.memH1a haU hu)).1
  have hGI := (Weighted.memH1a_memW11 hU hneU haU (Weighted.MemH1a0.memH1a haU hu)).2.2.2.2
  obtain ⟨huM, hGM, φ, hφ, hc, hlocal, hEu⟩ := hu
  have hcore (n : ℕ) := Weighted.isSmoothCore_of_supported haU (hφ n).1 (hφ n).2.1
  have hL := (Weighted.core_tendsto_l1 hU hneU haU hcore hc huM hlocal).2
  have huV : IntegrableOn (U.indicator u) V := by
    change Integrable (U.indicator u) (volume.restrict V)
    rw [integrable_indicator_iff hU.isOpen.measurableSet]
    change Integrable u ((volume.restrict V).restrict U)
    rw [Measure.restrict_restrict hU.isOpen.measurableSet, inter_eq_left.mpr hUV]
    exact huI
  have hGV : AEStronglyMeasurable (U.indicator G) (volume.restrict V) := by
    rw [aestronglyMeasurable_indicator_iff hU.isOpen.measurableSet]
    rw [Measure.restrict_restrict hU.isOpen.measurableSet, inter_eq_left.mpr hUV]
    exact hGM
  let H : Weighted.GradientCore ha := ⟨U.indicator G, hGV,
    Weighted.quadratic_integrable ha hGV (by change weightedEnergy a V (U.indicator G) < ⊤; rw [lift_energy_indicator hU.isOpen.measurableSet hUV]; exact hGI)⟩
  let fV : ℕ → Weighted.supportedCoreSubmodule V := fun n =>
    ⟨φ n, (hφ n).1, (hφ n).2.1, (hφ n).2.2.trans hUV⟩
  have hLv : Tendsto (fun n => eLpNorm ((fV n).val - U.indicator u) 1 (volume.restrict V)) atTop (𝓝 0) := by
    have he (n : ℕ) : (fV n).val - U.indicator u = U.indicator (φ n - u) := by
      change φ n - U.indicator u = U.indicator (φ n - u)
      rw [show U.indicator (φ n - u) = U.indicator (φ n) - U.indicator u from indicator_sub U _ _,
        lift_supported_eq_indicator (hφ n).2.2]
    simp_rw [he, eLpNorm_indicator_eq_eLpNorm_restrict hU.isOpen.measurableSet,
      Measure.restrict_restrict hU.isOpen.measurableSet, inter_eq_left.mpr hUV]
    exact hL
  have hEv : Tendsto (fun n => weightedEnergy a V (smoothGrad (fV n).val - H.field)) atTop (𝓝 0) := by
    have he (n : ℕ) : smoothGrad (fV n).val - H.field = U.indicator (smoothGrad (φ n) - G) := by
      change smoothGrad (φ n) - U.indicator G = U.indicator (smoothGrad (φ n) - G)
      rw [show U.indicator (smoothGrad (φ n) - G) = U.indicator (smoothGrad (φ n)) - U.indicator G from indicator_sub U _ _,
        lift_supported_gradient_eq_indicator (hφ n).2.2]
    simp_rw [he, lift_energy_indicator hU.isOpen.measurableSet hUV]
    exact hEu
  exact Weighted.memH1a0_of_graph_tendsto_and_l1 hV ha huV hLv
    (Weighted.smoothGraph_tendsto_of_l1_energy hV ha
      (f := fun n => Weighted.supportedToSmooth hV ha (fV n)) hLv hEv)

end
end CoarseDeGiorgi.Whitney
