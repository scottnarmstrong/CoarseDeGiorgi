import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Data.EReal.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsSmoothCore
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.CubeSurface
import CoarseDeGiorgi.Statements.H1aWeightedNorm
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PositiveCap
import CoarseDeGiorgi.Statements.PositiveCapGradient
import CoarseDeGiorgi.Statements.SampledResponseSeries
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.SmoothGrad
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
import CoarseDeGiorgi.Statements.SurfaceFracNorm
import CoarseDeGiorgi.Statements.SurfaceMeasure
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.WeightedEnergy

import CoarseDeGiorgi.Assembly.ParameterDefs
import CoarseDeGiorgi.GoodRadius.Hypothesis
import CoarseDeGiorgi.GoodRadius.TruncationTransfer
import CoarseDeGiorgi.GoodRadius.TraceData
import CoarseDeGiorgi.GoodRadius.Selection
import CoarseDeGiorgi.Harnack.Selection.Cap
import CoarseDeGiorgi.Harnack.WeakHarnack.SelectionAdapters
import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
import CoarseDeGiorgi.Weighted.PairOperations

/-!
# Proposition `p.good.radius` from the localization of Proposition `p.fractional.localization`

A good-radius selection with fractional and L² trace convergence, proved from the localization statement
`FractionalLocalizationHyp` (the verbatim conclusion of Proposition `p.fractional.localization`)
as an explicit hypothesis, in every dimension `d ≥ 3`.
-/

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.GoodRadius

theorem good_radius_of_localization
    (hloc : ∀ d : ℕ, 3 ≤ d → FractionalLocalizationHyp d) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
            MemH1a a (originCube 1) v G →
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ v x) →
            ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              eLpNorm v (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube ρ₂)) < ⊤ →
              ∀ vᵢ : ℕ → Vec d → ℝ,
                (∀ i, IsSmoothCore a (originCube 1) (vᵢ i)) →
                (∀ i, ∀ x ∈ originCube (d := d) 1, 0 ≤ vᵢ i x) →
                Filter.Tendsto
                  (fun i => h1aWeightedNorm a (originCube 1)
                    (fun x => vᵢ i x - v x)
                    (fun x => smoothGrad (vᵢ i) x - G x))
                  Filter.atTop (nhds 0) →
                ∃ τ ∈ selectionInterval ρ₁ ρ₂, ∃ ns : ℕ → ℕ, StrictMono ns ∧
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N →
                    Filter.Tendsto
                      (fun i => surfaceFracNorm τ (alphaParam t) (paramR q)
                        (fun x => positiveCap (vᵢ (ns i)) k N x - positiveCap v k N x))
                      Filter.atTop (nhds 0) ∧
                    Filter.Tendsto
                      (fun i => eLpNorm
                        (fun x => positiveCap (vᵢ (ns i)) k N x - positiveCap v k N x)
                        2 (surfaceMeasure τ))
                      Filter.atTop (nhds 0)) ∧
                  sampledResponseSeries a ha s p τ ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / (2 * p))) *
                      (upperMoment a ha s p hs (le_of_lt hp)).rpow (1 / 2) ∧
                  surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁))⁻¹ *
                      weightedEnergy a (originCube ρ₂) G ∧
                  surfaceFracNorm τ (alphaParam t) (paramR q) v ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-alphaParam t - 1 / paramR q) *
                      ((lowerMoment a ha t q ht (le_of_lt hq)).rpow (-(1 / 2)) *
                        (weightedEnergy a (originCube ρ₂) G).rpow (1 / 2) +
                        eLpNorm v (ENNReal.ofReal (paramR q))
                          (volume.restrict (originCube ρ₂))) ∧
                  eLpNorm v (ENNReal.ofReal (paramR q)) (surfaceMeasure τ) ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / paramR q)) *
                      eLpNorm v (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube ρ₂)) ∧
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N → ∀ τ' : ℝ,
                    surfaceEnergyMaximal ρ₁ ρ₂ a ha (positiveCapGradient v G k N) τ' ≤
                      surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ') ∧
                  (eLpNorm v 2 (volume.restrict (originCube ρ₂)) < ⊤ →
                    eLpNorm v 2 (surfaceMeasure τ) ≤
                      C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / 2)) *
                        eLpNorm v 2 (volume.restrict (originCube ρ₂)))
:= by
  intro d hd
  cases d with
  | zero => omega
  | succ n =>
  intro p q s t hp hq hs ht hθ
  have : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  obtain ⟨S, φ, S', φ', hcover, hrest⟩ := hloc (n + 1) hd
  obtain ⟨Cl, hClTop, hCl⟩ := hrest p q s t hp hq hs ht hθ
  obtain ⟨C, hC0, hCtop, hsel⟩ := selection_bounds n hd p q s t hp hq hs ht hθ Cl hClTop
  obtain ⟨hα, hα1, hr, _⟩ := Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  refine ⟨C, hCtop, ?_⟩
  intro a ha hrange v G hv hvnn ρ₁ ρ₂ hρ hgap hR hvq vi hsmooth hnn hnorm
  have hδ : 0 < ρ₂ - ρ₁ := sub_pos.mpr hgap
  have hρ0 : 0 ≤ ρ₁ := by linarith only [hρ]
  have hcov := hcover ρ₁ ρ₂ hρ hgap hR
  have hφ : ∀ i ∈ S ρ₁ ρ₂, ContDiff ℝ (⊤ : ℕ∞) (φ ρ₁ ρ₂ i) := fun i hi => (hcov.1 i hi).2.1
  have hL : LocalizationClause a ha q t hq ht (S ρ₁ ρ₂) (φ ρ₁ ρ₂) ρ₁ ρ₂ Cl :=
    (hCl a ha hrange ρ₁ ρ₂ hρ hgap hR).1
  obtain ⟨w₀, W, hw₀m, hWm, hw₀v, hWvi, hbd, hsurf, ns, hns, hgood⟩ :=
    trace_data hd hp hq hs ht hθ a ha hρ hgap hR hφ hL v G hv vi hsmooth hnorm
  have hw₀mem : MemH1a a (originCube 1) w₀ G :=
    Weighted.MemH1a.congr_ae hv hw₀v.symm EventuallyEq.rfl
  have hFm := measurable_localized_sum hφ hw₀m
  have hsub : originCube (d := n + 1) ρ₂ ⊆ originCube 1 := Assembly.caccioppoli_cube_mono hR
  have heLp : ∀ b : ℝ≥0∞, eLpNorm v b (volume.restrict (originCube ρ₂)) =
      eLpNorm w₀ b (volume.restrict (originCube ρ₂)) := fun b =>
    eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hw₀v.symm)
  have hbd' := hbd
  rw [heLp] at hbd'
  obtain ⟨τ, hτ, hgd, hresp, hmaxG, hfrac, hLr, hL2b⟩ :=
    hsel a ha hrange w₀ _ G hw₀mem hw₀m hFm ρ₁ ρ₂ hρ hgap hR
      (hsurf.mono fun _ h => h.1) hbd'
      (fun τ => ((∑' i, surfaceFracNorm τ (alphaParam t) (paramR q)
          (fun x => W (ns i) x - w₀ x) ^ paramR q ≠ ⊤) ∧
        Tendsto (fun i => eLpNorm (fun x => W (ns i) x - w₀ x) 2 (surfaceMeasure τ))
          atTop (𝓝 0)) ∧
        ((fun x => ∑ i ∈ S ρ₁ ρ₂, φ ρ₁ ρ₂ i x * w₀ x) =ᵐ[surfaceMeasure τ] w₀ ∧
          w₀ =ᵐ[surfaceMeasure τ] v ∧ ∀ i, W i =ᵐ[surfaceMeasure τ] vi i))
      (by filter_upwards [hsurf, hgood] with τ h1 h2; exact ⟨h2, h1⟩)
  obtain ⟨⟨hsum, hL2⟩, _, hwv, hWv⟩ := hgd
  have hδ' := sub_pos.mpr hgap
  -- finiteness of the fractional norm of `w₀` on the surface
  have hEfin : weightedEnergy a (originCube ρ₂) G ≠ ⊤ :=
    ((lintegral_mono_set hsub).trans_lt
      (Weighted.MemH1a.energy_lt_top
        (Assembly.hybrid_unitCube_domain (d := n + 1)).1.isOpen ha hw₀mem)).ne
  have hlam := (Assembly.caccioppoli_moments_finite (ha := ha) hp hq hs ht hrange).2.1
  have hlamTop : (lowerMoment a ha t q ht hq.le).rpow (-(1 / 2)) ≠ ⊤ := by
    simp only [ENNReal.rpow_eq_pow]
    rw [ENNReal.rpow_neg]
    exact ENNReal.inv_ne_top.mpr (ENNReal.rpow_pos_of_nonneg hlam (by norm_num)).ne'
  have hrpowTop : ∀ y : ℝ, (ENNReal.ofReal (ρ₂ - ρ₁)).rpow y ≠ ⊤ := fun y => by
    simp only [ENNReal.rpow_eq_pow]
    rw [ENNReal.ofReal_rpow_of_pos hδ']
    exact ENNReal.ofReal_ne_top
  have hfin : surfaceFracNorm τ (alphaParam t) (paramR q) w₀ ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hfrac
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top hCtop.ne (hrpowTop _))
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hlamTop ?_, ?_⟩)
    · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hEfin).ne
    · rw [← heLp]; exact hvq.ne
  -- the `a.e.` agreement of truncations at `τ`
  have hcapAE : ∀ (f g : Vec (n + 1) → ℝ) (k : ℝ) (N : ℝ≥0∞),
      f =ᵐ[surfaceMeasure τ] g →
      positiveCap f k N =ᵐ[surfaceMeasure τ] positiveCap g k N := by
    intro f g k N h
    filter_upwards [h] with x hx
    simp only [positiveCap, positivePart, hx]
  have hτrange : τ ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
    have hI := CoarseDeGiorgi.Selection.selectionInterval_subset hgap hτ
    constructor <;> linarith [hI.1, hI.2, hρ, hR]
  have hgradEq : ∀ (c : ℝ) (N : ℝ≥0∞), Harnack.Selection.selectionCapGradient c N v G =
      positiveCapGradient v G c N := by
    intro c N
    funext x
    by_cases htop : N = ⊤
    · simp [Harnack.Selection.selectionCapGradient, positiveCapGradient,
        positiveTruncationGradient, htop, Set.indicator_apply]
    · simp [Harnack.Selection.selectionCapGradient, positiveCapGradient,
        htop, Set.indicator_apply]
  have henergyEq : CoarseDeGiorgi.Selection.surfaceEnergyMaximal ρ₁ ρ₂
      (fun x => ENNReal.ofReal (vecDot (G x) (matVecMul (a x) (G x)))) τ =
        surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ :=
    Harnack.WeakHarnack.sourceSurfaceEnergyMaximal_eq_statement ρ₁ ρ₂ a ha G τ
  have hInv : (ENNReal.ofReal (ρ₂ - ρ₁))⁻¹ = ENNReal.ofReal ((ρ₂ - ρ₁) ^ (-1 : ℝ)) := by
    rw [Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos hδ']
  refine ⟨τ, hτ, ns, hns, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- convergence for every truncation
    intro k N _hN
    obtain ⟨h1, h2⟩ := truncations_tendsto (u := fun i => W (ns i)) hr hw₀m (fun i => hWm (ns i)) hfin hsum hL2 k N
    have hcongr (i : ℕ) : (fun x => positiveCap (vi (ns i)) k N x - positiveCap v k N x)
        =ᵐ[surfaceMeasure τ]
        (fun x => positiveCap (W (ns i)) k N x - positiveCap w₀ k N x) :=
      ((hcapAE _ _ k N (hWv (ns i)).symm)).sub (hcapAE _ _ k N hwv.symm)
    refine ⟨?_, ?_⟩
    · simpa only [CoarseDeGiorgi.Selection.surfaceFracNorm_congr_ae (hcongr _)] using h1
    · simpa only [eLpNorm_congr_ae (hcongr _)] using h2
  · have hresp' := hresp
    rw [Harnack.WeakHarnack.sourceSampledSeries_eq_statement a ha s p τ hτrange] at hresp'
    rw [← ENNReal.ofReal_rpow_of_pos hδ'] at hresp'
    exact hresp'
  · rw [← henergyEq]
    refine hmaxG.trans ?_
    rw [hInv]
  · rw [← CoarseDeGiorgi.Selection.surfaceFracNorm_congr_ae hwv, heLp]
    exact hfrac
  · rw [← eLpNorm_congr_ae hwv, heLp]
    have hLr' := hLr
    rw [← ENNReal.ofReal_rpow_of_pos hδ'] at hLr'
    exact hLr'
  · intro k N _hN τ'
    have hmono := CoarseDeGiorgi.Selection.source_surfaceEnergyMaximal_mono_ae (n := n)
      (ρ := ρ₁) (R := ρ₂) hρ0
      (Eventually.of_forall (Harnack.Selection.selectionCap_density_le a v G k N)) τ'
    rw [hgradEq] at hmono
    rw [Harnack.WeakHarnack.sourceSurfaceEnergyMaximal_eq_statement ρ₁ ρ₂ a ha] at hmono
    rw [Harnack.WeakHarnack.sourceSurfaceEnergyMaximal_eq_statement ρ₁ ρ₂ a ha] at hmono
    exact hmono
  · intro _hL2fin
    rw [← eLpNorm_congr_ae hwv, heLp]
    have hL2' := hL2b
    rw [← ENNReal.ofReal_rpow_of_pos hδ'] at hL2'
    exact hL2'

end CoarseDeGiorgi.GoodRadius
