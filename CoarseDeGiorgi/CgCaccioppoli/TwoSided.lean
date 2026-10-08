import Homogenization.Ambient.CoefficientField
import Homogenization.Sobolev.WeakDerivatives
import Homogenization.CoarseGraining.Definitions
import Homogenization.Geometry.TriadicCube
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import CoarseDeGiorgi.Statements.IsSmoothCore
import CoarseDeGiorgi.Statements.IsTriadicWidth
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.IsWeightedSubsolution
import CoarseDeGiorgi.Statements.MemH1a
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.H1aWeightedNorm
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.PositiveCap
import CoarseDeGiorgi.Statements.PositiveCapGradient
import CoarseDeGiorgi.Statements.SampledResponseSeries
import CoarseDeGiorgi.Statements.SelectionInterval
import CoarseDeGiorgi.Statements.SigmaUpper
import CoarseDeGiorgi.Statements.SmoothGrad
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.SurfaceEnergyMaximal
import CoarseDeGiorgi.Statements.SurfaceFracNorm
import CoarseDeGiorgi.Statements.SurfaceFracSeminorm
import CoarseDeGiorgi.Statements.SurfaceMeasure
import CoarseDeGiorgi.Statements.WeightedEnergy
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.GoodRadiusExists
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Selection.SourceNonnegative
import CoarseDeGiorgi.Assembly.TwoSidedUniformArithmetic
import CoarseDeGiorgi.Assembly.TwoSidedUniformSelection
import CoarseDeGiorgi.Assembly.CaccioppoliWindow
import CoarseDeGiorgi.CgCaccioppoli.Truncation

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.CgCaccioppoli

/-- The one-surface estimate at a good radius, from Proposition `p.good.radius` and Proposition `p.good.radius.energy`: for every triadic width `h ≤ δ/(20000 d)`, the
inner energy is bounded by `C δ^{-γ₁}(Θ^{1/2} h^θ E + Λ^{1/2} h^{-σ} ‖v‖₂ E^{1/2})`. -/
theorem two_sided_of_energy (h72 :

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
                ∀ τ ∈ selectionInterval ρ₁ ρ₂, ∀ ns : ℕ → ℕ, StrictMono ns →
                  ∀ C₅ : ℝ≥0∞, C₅ < ⊤ →
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N →
                    Filter.Tendsto
                      (fun i => surfaceFracNorm τ (alphaParam t) (paramR q)
                        (fun x => positiveCap (vᵢ (ns i)) k N x - positiveCap v k N x))
                      Filter.atTop (nhds 0)) →
                  sampledResponseSeries a ha s p τ ≤
                    C₅ * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow (-(1 / (2 * p))) *
                      (upperMoment a ha s p hs (le_of_lt hp)).rpow (1 / 2) →
                  surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ ≤
                    C₅ * (ENNReal.ofReal (ρ₂ - ρ₁))⁻¹ *
                      weightedEnergy a (originCube ρ₂) G →
                  (∀ k : ℝ, ∀ N : ℝ≥0∞, 0 < N → ∀ τ' : ℝ,
                    surfaceEnergyMaximal ρ₁ ρ₂ a ha (positiveCapGradient v G k N) τ' ≤
                      surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ') →
                  ∀ k : ℝ,
                    IsWeightedSubsolution a (originCube 1) (positiveCap v k ⊤)
                      (positiveCapGradient v G k ⊤) →
                    ∀ h : ℝ, IsTriadicWidth h → h ≤ (ρ₂ - ρ₁) / (20000 * (d : ℝ)) →
                      weightedEnergy a (originCube τ) (positiveCapGradient v G k ⊤) ≤
                        C * sampledResponseSeries a ha s p τ *
                          (surfaceEnergyMaximal ρ₁ ρ₂ a ha G τ).rpow (1 / 2) *
                          ((ENNReal.ofReal h).rpow (paramTheta d p q s t) *
                            surfaceFracSeminorm τ (alphaParam t) (paramR q)
                              (positiveCap v k ⊤) +
                            (ENNReal.ofReal h).rpow (-(sigmaUpper d p s)) *
                              eLpNorm (positiveCap v k ⊤) 2 (surfaceMeasure τ))) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d), (ha : IsWeightedCoeffOn (originCube 1) a) →
          spatialMomentRange a ha p q s t →
          ∀ (v : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ v x) →
            IsWeightedSubsolution a (originCube 1) v G →
            ∀ ρ R : ℝ, (1 / 2 : ℝ) ≤ ρ → ρ < R → R ≤ 1 →
              ∀ n : ℤ, (3 : ℝ) ^ n ≤ (R - ρ) / (20000 * (d : ℝ)) →
                weightedEnergy a (originCube ρ) G ≤
                  C * (ENNReal.ofReal (R - ρ)).rpow (-gammaLoc p q t) *
                    ((contrast a ha s t p q hs ht hp.le hq.le).rpow (1 / 2) *
                      (ENNReal.ofReal ((3 : ℝ) ^ n)).rpow (paramTheta d p q s t) *
                      weightedEnergy a (originCube R) G +
                    (upperMoment a ha s p hs hp.le).rpow (1 / 2) *
                      (ENNReal.ofReal ((3 : ℝ) ^ n)).rpow (-(sigmaUpper d p s)) *
                      eLpNorm v 2 (volume.restrict (originCube R)) *
                      (weightedEnergy a (originCube R) G).rpow (1 / 2)) := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have : NeZero (n + 1) := ⟨by omega⟩
  obtain ⟨C₅, hC₅, hgr⟩ := CoarseDeGiorgi.good_radius_exists (n + 1) hd p q s t hp hq hs ht hθ
  obtain ⟨K₇, hK₇, h7⟩ := h72 (n + 1) hd p q s t hp hq hs ht hθ
  let K' := K₇ * C₅ ^ (1 / 2 : ℝ)
  let B := K' * C₅ * (192 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (C₅ + C₅)
  have hB : B ≠ ⊤ := by dsimp [B, K']; finiteness
  refine ⟨2 * B + 1, by finiteness, ?_⟩
  intro a ha hrange v G hvpos hv ρ R hρ hgap hR
  obtain ⟨hU, hL, _⟩ := Assembly.caccioppoli_moments_finite (ha := ha) hp hq hs ht hrange
  change upperMoment a ha s p hs hp.le < ⊤ at hU
  change 0 < lowerMoment a ha t q ht hq.le at hL
  let E := weightedEnergy a (originCube R) G
  let N := eLpNorm v 2 (volume.restrict (originCube R))
  have hE : E ≠ ⊤ := (Assembly.caccioppoli_energy_finite ha hv hR).ne
  have hδ : 0 < R - ρ := sub_pos.mpr hgap
  have hδ1 : R - ρ ≤ 1 := by linarith only [hρ, hR]
  have hwidth (k : ℤ) (hk : (3 : ℝ) ^ k ≤ (R - ρ) / (20000 * ((n + 1 : ℕ) : ℝ))) :
      (3 : ℝ) ^ k ≤ 1 := by
    have hdr : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hd
    have hden : 0 < 20000 * ((n + 1 : ℕ) : ℝ) := by positivity
    exact hk.trans ((div_le_one hden).mpr (hδ1.trans (by linarith only [hdr])))
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hm : 0 < sigmaUpper (n + 1) p s := by
    have hdr : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hd
    unfold sigmaUpper
    exact add_pos hs (div_pos (by linarith only [hdr]) (by positivity))
  by_cases he0 : E = 0
  · intro k _hk
    have heinner := Assembly.caccioppoli_energy_mono a G hgap.le
    change weightedEnergy a (originCube ρ) G ≤ E at heinner
    rw [he0] at heinner
    exact heinner.trans bot_le
  by_cases hN : N = ⊤
  · intro k hk
    have hh : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
    have hUp := Assembly.two_sided_upper_moment_pos (by omega : 0 < n + 1) a ha hs hp.le
    have hcoef : upperMoment a ha s p hs hp.le ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((3 : ℝ) ^ k) ^ (-(sigmaUpper (n + 1) p s)) ≠ 0 :=
      mul_ne_zero (ENNReal.rpow_pos hUp hU.ne).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hh) ENNReal.ofReal_ne_top).ne'
    have hEh : E ^ (1 / 2 : ℝ) ≠ 0 :=
      (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr he0) hE).ne'
    have hpre : (2 * B + 1) * ENNReal.ofReal (R - ρ) ^ (-gammaLoc p q t) ≠ 0 :=
      mul_ne_zero (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
        (le_add_left le_rfl)))
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hδ) ENNReal.ofReal_ne_top).ne'
    change weightedEnergy a (originCube ρ) G ≤
      (2 * B + 1) * ENNReal.ofReal (R - ρ) ^ (-gammaLoc p q t) *
        (contrast a ha s t p q hs ht hp.le hq.le ^ (1 / 2 : ℝ) *
          ENNReal.ofReal ((3 : ℝ) ^ k) ^ paramTheta (n + 1) p q s t * E +
          upperMoment a ha s p hs hp.le ^ (1 / 2 : ℝ) *
            ENNReal.ofReal ((3 : ℝ) ^ k) ^ (-(sigmaUpper (n + 1) p s)) * N *
              E ^ (1 / 2 : ℝ))
    rw [hN, ENNReal.mul_top hcoef, ENNReal.top_mul hEh, add_top, ENNReal.mul_top hpre]
    exact le_top
  have hNlt : N < ⊤ := lt_top_iff_ne_top.mpr hN
  have hvR : AEStronglyMeasurable v (volume.restrict (originCube R)) :=
    hv.1.1.mono_measure (Measure.restrict_mono (Assembly.caccioppoli_cube_mono hR) le_rfl)
  have hlr := Assembly.two_sided_lr_le_l2 hq hR hvR
  have hunit := Assembly.hybrid_unitCube_domain (d := n + 1)
  obtain ⟨vi, hvi, hL1, hEv⟩ := Selection.source_nonnegative_approximation
    hunit.1 hunit.2 ha hv.1 hvpos
  have hnorm := h1aWeightedNorm_tendsto_of_l1_energy (a := a)
    (w := fun i x => vi i x - v x) (G := fun i x => smoothGrad (vi i) x - G x) hL1 hEv
  obtain ⟨τ, hτ, ns, hns, hconv, hS, hD, hF, -, hcapmax, hZ⟩ :=
    hgr a ha hrange v G hv.1 hvpos ρ R hρ hgap hR (hlr.trans_lt hNlt) vi
      (fun i => (hvi i).1) (fun i x _ => (hvi i).2 x) hnorm
  have hτI := Selection.selectionInterval_subset hgap hτ
  intro k hk
  have hh : 0 < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hh1 := hwidth k hk
  have hk0 : k ≤ 0 := by
    by_contra hpos
    replace hpos := not_le.mp hpos
    have := one_lt_zpow₀ (by norm_num : (1 : ℝ) < 3) hpos
    linarith
  have htri : IsTriadicWidth ((3 : ℝ) ^ k) := ⟨(-k).toNat, by congr 1; omega⟩
  have hsub0 := isWeightedSubsolution_positiveCap_zero hunit.1 hunit.2 ha hv hvpos
  have hb := h7 a ha hrange v G hv.1 hvpos ρ R hρ hgap hR (hlr.trans_lt hNlt) vi
    (fun i => (hvi i).1) (fun i x _ => (hvi i).2 x) hnorm τ hτ ns hns C₅ hC₅ hconv hS hD
    hcapmax 0 hsub0 ((3 : ℝ) ^ k) htri hk
  have hEτ : weightedEnergy a (originCube τ) (positiveCapGradient v G 0 ⊤) =
      weightedEnergy a (originCube τ) G := by
    rw [positiveCapGradient_zero_top]
    apply Weighted.energy_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset
      (Assembly.caccioppoli_cube_mono (hτI.2.le.trans hR))
      (Weighted.nonnegative_pair_posPart_ae hunit.1 hunit.2 ha hv.1 hvpos).2
  obtain ⟨hα, _, hr0, hr2, -⟩ := Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  change 0 < alphaParam t at hα
  change 1 < paramR q at hr0
  change paramR q < 2 at hr2
  have hsemi : surfaceFracSeminorm τ (alphaParam t) (paramR q) v ≤
      surfaceFracNorm τ (alphaParam t) (paramR q) v := by
    unfold surfaceFracNorm
    have hh := ENNReal.rpow_le_rpow (le_add_left le_rfl :
      surfaceFracSeminorm τ (alphaParam t) (paramR q) v ^ paramR q ≤
        eLpNorm v (ENNReal.ofReal (paramR q)) (surfaceMeasure τ) ^ paramR q +
          surfaceFracSeminorm τ (alphaParam t) (paramR q) v ^ paramR q)
      (show 0 ≤ 1 / paramR q by positivity)
    simpa only [ENNReal.rpow_eq_pow, ← ENNReal.rpow_mul,
      mul_one_div_cancel (zero_lt_one.trans hr0).ne', ENNReal.rpow_one] using hh
  have hFw : surfaceFracSeminorm τ (alphaParam t) (paramR q) (positiveCap v 0 ⊤) ≤
      surfaceFracNorm τ (alphaParam t) (paramR q) v :=
    (surfaceFracSeminorm_positiveCap_le _ _ _ (zero_lt_one.trans hr0) v).trans hsemi
  have hZw := eLpNorm_positiveCap_le v (surfaceMeasure τ)
  let D := (192 : ℝ≥0∞) * (ENNReal.ofReal (R - ρ))⁻¹ * E
  have hD' : surfaceEnergyMaximal ρ R a ha G τ ≤ C₅ * D := by
    apply hD.trans
    have h192 : (ENNReal.ofReal (R - ρ))⁻¹ * E ≤ 192 * (ENNReal.ofReal (R - ρ))⁻¹ * E := by
      rw [mul_assoc]
      exact le_mul_of_one_le_left' (by norm_num)
    calc C₅ * (ENNReal.ofReal (R - ρ))⁻¹ * weightedEnergy a (originCube R) G
        = C₅ * ((ENNReal.ofReal (R - ρ))⁻¹ * E) := mul_assoc _ _ _
      _ ≤ C₅ * D := mul_le_mul' le_rfl h192
  simp only [ENNReal.rpow_eq_pow] at hb hS hF hZ
  have hdroot := ENNReal.rpow_le_rpow hD' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hdroot
  have hb' : weightedEnergy a (originCube τ) G ≤ K' * sampledResponseSeries a ha s p τ *
      D ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal ((3 : ℝ) ^ k) ^ paramTheta (n + 1) p q s t *
          surfaceFracNorm τ (alphaParam t) (paramR q) v +
        ENNReal.ofReal ((3 : ℝ) ^ k) ^ (-(sigmaUpper (n + 1) p s)) *
          eLpNorm v 2 (surfaceMeasure τ)) := by
    rw [← hEτ]
    apply hb.trans
    calc _ ≤ K₇ * sampledResponseSeries a ha s p τ * (C₅ ^ (1 / 2 : ℝ) * D ^ (1 / 2 : ℝ)) *
        (ENNReal.ofReal ((3 : ℝ) ^ k) ^ paramTheta (n + 1) p q s t *
            surfaceFracNorm τ (alphaParam t) (paramR q) v +
          ENNReal.ofReal ((3 : ℝ) ^ k) ^ (-(sigmaUpper (n + 1) p s)) *
            eLpNorm v 2 (surfaceMeasure τ)) := by gcongr
      _ = _ := by dsimp [K']; ring
  have hr' : 1 / paramR q = 1 / 2 + 1 / (2 * q) := by
    have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
    have hq1 : q + 1 ≠ 0 := by linarith only [hq]
    unfold paramR
    field_simp
  have hexp : 1 / (2 * p) + 1 / 2 + (alphaParam t + 1 / paramR q) = gammaLoc p q t := by
    rw [hr']
    unfold gammaLoc alphaParam
    ring
  have hbexp : 1 / 2 ≤ alphaParam t + 1 / paramR q := by
    rw [hr']
    have : 0 < 1 / (2 * q) := by positivity
    linarith only [hα, this]
  have hF' : surfaceFracNorm τ (alphaParam t) (paramR q) v ≤
      C₅ * ENNReal.ofReal (R - ρ) ^ (-(alphaParam t + 1 / paramR q)) *
        (lowerMoment a ha t q ht hq.le ^ (-1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) + N) := by
    have e1 : -alphaParam t - 1 / paramR q = -(alphaParam t + 1 / paramR q) := by ring
    have e2 : -(1 / 2 : ℝ) = -1 / 2 := by ring
    rw [e1, e2] at hF
    exact hF.trans (mul_le_mul' le_rfl (add_le_add le_rfl hlr))
  have hZ' : eLpNorm v 2 (surfaceMeasure τ) ≤
      C₅ * ENNReal.ofReal (R - ρ) ^ (-1 / 2 : ℝ) * N := by
    have e2 : -(1 / 2 : ℝ) = -1 / 2 := by ring
    have := hZ hNlt
    rw [e2] at this
    exact this
  have hmul := Assembly.two_sided_uniform_multiply hδ hδ1 hbexp hexp hS hF' hZ'
    (le_refl D) hb'
  have helim := Assembly.two_sided_uniform_eliminate hδ hδ1 hh hh1 hθ.le hm.le hmul
  apply ((Assembly.caccioppoli_energy_mono a G hτI.1.le).trans helim).trans
  exact mul_le_mul' (mul_le_mul' (le_add_right le_rfl) le_rfl) le_rfl

end CoarseDeGiorgi.CgCaccioppoli
