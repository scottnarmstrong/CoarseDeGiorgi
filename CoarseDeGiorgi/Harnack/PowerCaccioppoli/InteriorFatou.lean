import CoarseDeGiorgi.Harnack.PowerLimits.SignedInterior
import CoarseDeGiorgi.Harnack.Selection.Cap
import CoarseDeGiorgi.Weighted.Energy
import Homogenization.Ambient.CoefficientField

/-! # Fatou passage for the signed interior term -/

namespace CoarseDeGiorgi.Harnack.PowerCaccioppoli

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-- An `L¹` approximation has an almost-everywhere convergent strict
subsequence, for use in the quotient-density Fatou passage below. -/
theorem exists_subsequence_ae_of_L1_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  obtain ⟨ns, hns, hconv⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by norm_num : (1 : ℝ≥0∞) ≠ 0) h).exists_seq_tendsto_ae
  exact ⟨ns, hns, hconv⟩

/-- Pointwise convergence of the nonnegative test values is enough for a lower
limit of their quotient integrals. This is the direction needed to pass the
signed test inequality to the capped energy; it does not require a uniform
majorant for the smooth approximants.
-/
theorem ratio_lintegral_le_liminf_of_pointwise
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (den q : α → ℝ) (w : ℕ → α → ℝ) (wlim : α → ℝ)
    (hden : ∀ᵐ x ∂μ, den x ≠ 0)
    (hW : ∀ n, AEStronglyMeasurable
      (fun x => ENNReal.ofReal ((w n x / den x) * q x)) μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => w n x) atTop (𝓝 (wlim x))) :
    ∫⁻ x, ENNReal.ofReal ((wlim x / den x) * q x) ∂μ ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal ((w n x / den x) * q x) ∂μ) atTop := by
  have hquotient : ∀ᵐ x ∂μ, Tendsto
      (fun n => ENNReal.ofReal ((w n x / den x) * q x)) atTop
      (𝓝 (ENNReal.ofReal ((wlim x / den x) * q x))) := by
    filter_upwards [hden, hpoint] with x hxden hxlim
    have hcont : Continuous (fun y : ℝ => ENNReal.ofReal ((y / den x) * q x)) := by
      exact ENNReal.continuous_ofReal.comp (by fun_prop)
    exact hcont.continuousAt.tendsto.comp hxlim
  have hlim : (fun x => liminf
      (fun n => ENNReal.ofReal ((w n x / den x) * q x)) atTop) =ᵐ[μ]
      (fun x => ENNReal.ofReal ((wlim x / den x) * q x)) := by
    filter_upwards [hquotient] with x hx
    exact hx.liminf_eq
  calc
    ∫⁻ x, ENNReal.ofReal ((wlim x / den x) * q x) ∂μ =
        ∫⁻ x, liminf
          (fun n => ENNReal.ofReal ((w n x / den x) * q x)) atTop ∂μ :=
      lintegral_congr_ae hlim.symm
    _ ≤ liminf (fun n => ∫⁻ x,
        ENNReal.ofReal ((w n x / den x) * q x) ∂μ) atTop :=
      lintegral_liminf_le' fun n => (hW n).aemeasurable

/-- Combine the pointwise Fatou passage with the exact positive-cap ratio
comparison. The result is the capped-energy lower bound required by the
signed testing limit.
-/
theorem positive_cap_energy_le_liminf_ratio_integrals
    {d : ℕ} [NeZero d] {V : Set (Vec d)} (hV : IsOpen V)
    (a : CoeffField d) (ha : IsWeightedCoeffOn V a)
    {v : Vec d → ℝ} {G : Vec d → Vec d} {N : ℝ≥0∞}
    (hcap : MemH1a a V
      (Selection.selectionCap 0 N v)
      (Selection.selectionCapGradient 0 N v G))
    (hpositive : ∀ᵐ x ∂volume.restrict V, 0 < v x)
    (hNtop : N ≠ ⊤)
    (hcapRatio : IntegrableOn (fun x =>
      (Selection.selectionCap 0 N v x / v x) *
        vecDot (G x) (matVecMul (a x) (G x))) V)
    (hcapRatioNonneg : 0 ≤ᵐ[volume.restrict V] (fun x =>
      (Selection.selectionCap 0 N v x / v x) *
        vecDot (G x) (matVecMul (a x) (G x))))
    (w : ℕ → Vec d → ℝ)
    (hw : ∀ n, Integrable (fun x => (w n x / v x) *
      vecDot (G x) (matVecMul (a x) (G x))) (volume.restrict V))
    (hwNonneg : ∀ n, 0 ≤ᵐ[volume.restrict V] (fun x => (w n x / v x) *
      vecDot (G x) (matVecMul (a x) (G x))))
    (hpoint : ∀ᵐ x ∂volume.restrict V,
      Tendsto (fun n => w n x) atTop
        (𝓝 (Selection.selectionCap 0 N v x))) :
    weightedEnergy a V (Selection.selectionCapGradient 0 N v G) ≤
      liminf (fun n => ENNReal.ofReal (∫ x in V,
        (w n x / v x) * vecDot (G x) (matVecMul (a x) (G x)))) atTop := by
  let q : Vec d → ℝ := fun x => vecDot (G x) (matVecMul (a x) (G x))
  have hcapEnergy := Weighted.MemH1a.energy_lt_top hV ha hcap
  have hcapRatio' : IntegrableOn
      (fun x => (Selection.selectionCap 0 N v x / v x) * q x) V := by
    simpa only [q] using hcapRatio
  have hratioEnergy := PowerLimits.positive_cap_ratio_dominates_energy
    hV ha hcap hpositive hNtop hcapRatio'
  have hcapIntegralEq : ENNReal.ofReal
      (∫ x in V, (Selection.selectionCap 0 N v x / v x) * q x) =
      ∫⁻ x in V, ENNReal.ofReal
        ((Selection.selectionCap 0 N v x / v x) * q x) :=
    ofReal_integral_eq_lintegral_ofReal hcapRatio' hcapRatioNonneg
  have hcapEnergyLe : weightedEnergy a V
      (Selection.selectionCapGradient 0 N v G) ≤
      ∫⁻ x in V, ENNReal.ofReal
        ((Selection.selectionCap 0 N v x / v x) * q x) := by
    calc
      _ = ENNReal.ofReal (weightedEnergy a V
          (Selection.selectionCapGradient 0 N v G)).toReal :=
        (ENNReal.ofReal_toReal hcapEnergy.ne).symm
      _ ≤ ENNReal.ofReal (∫ x in V,
          (Selection.selectionCap 0 N v x / v x) * q x) :=
        ENNReal.ofReal_le_ofReal hratioEnergy
      _ = _ := hcapIntegralEq
  have hW (n : ℕ) : AEStronglyMeasurable
      (fun x => ENNReal.ofReal ((w n x / v x) * q x))
      (volume.restrict V) := by
    exact ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      ((hw n).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun x => rfl))
  have hden : ∀ᵐ x ∂volume.restrict V, v x ≠ 0 := by
    filter_upwards [hpositive] with x hx
    exact ne_of_gt hx
  have hFatou := ratio_lintegral_le_liminf_of_pointwise v q w
    (Selection.selectionCap 0 N v) hden hW hpoint
  have hseq (n : ℕ) : ENNReal.ofReal
      (∫ x in V, (w n x / v x) * q x) =
      ∫⁻ x in V, ENNReal.ofReal ((w n x / v x) * q x) :=
    ofReal_integral_eq_lintegral_ofReal (hw n) (hwNonneg n)
  have hFatou' :
      ∫⁻ x in V, ENNReal.ofReal
        ((Selection.selectionCap 0 N v x / v x) * q x) ≤
      liminf (fun n => ENNReal.ofReal
        (∫ x in V, (w n x / v x) * q x)) atTop := by
    calc
      _ ≤ liminf (fun n => ∫⁻ x in V,
          ENNReal.ofReal ((w n x / v x) * q x)) atTop := hFatou
      _ = _ := by
        apply Filter.liminf_congr
        exact Filter.Eventually.of_forall fun n => (hseq n).symm
  exact hcapEnergyLe.trans hFatou'

end CoarseDeGiorgi.Harnack.PowerCaccioppoli
