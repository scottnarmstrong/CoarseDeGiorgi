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
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Selection.SourceNonnegative
import CoarseDeGiorgi.Assembly.TwoSidedUniformArithmetic
import CoarseDeGiorgi.Assembly.TwoSidedUniformSelection
import CoarseDeGiorgi.CgCaccioppoli.Truncation
import CoarseDeGiorgi.Statements.GammaCacc
import CoarseDeGiorgi.Statements.SigmaLower
import CoarseDeGiorgi.Harnack.Moments.MomentComparison
import CoarseDeGiorgi.CgCaccioppoli.TwoSided
import CoarseDeGiorgi.Assembly.CaccioppoliWindow
import CoarseDeGiorgi.Assembly.CaccioppoliParameters

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.CgCaccioppoli

/-- The finite real expression of the window lemma, written in `ℝ≥0∞`. -/
theorem ofReal_expression_eq {Kc κ m' δ : ℝ} (hKc : 0 ≤ Kc) (hδ : 0 < δ) (hm' : 0 ≤ m')
    {U Θ N : ℝ≥0∞} (hU : U ≠ ⊤) (hΘ : Θ ≠ ⊤) (hN : N ≠ ⊤) :
    ENNReal.ofReal (Kc * δ ^ (-κ) * U.toReal * Θ.toReal ^ m' * N.toReal ^ 2) =
      ENNReal.ofReal Kc * ENNReal.rpow (ENNReal.ofReal δ) (-κ) * U *
        ENNReal.rpow Θ m' * ENNReal.rpow N 2 := by
  have h1 : 0 ≤ Kc * δ ^ (-κ) * U.toReal * Θ.toReal ^ m' := by positivity
  have h2 : 0 ≤ Kc * δ ^ (-κ) * U.toReal := by positivity
  have h3 : 0 ≤ Kc * δ ^ (-κ) := by positivity
  rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_mul h2, ENNReal.ofReal_mul h3,
    ENNReal.ofReal_mul hKc, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hm',
    ENNReal.ofReal_toReal hU, ENNReal.ofReal_toReal hΘ, ENNReal.ofReal_toReal hN]
  simp only [ENNReal.rpow_eq_pow, ENNReal.rpow_two, ENNReal.ofReal_rpow_of_pos hδ]

/-- The exponent bookkeeping: `2γ₁ + 2γ₁σ/θ = γ₂`. -/
theorem exponent_identity {d : ℕ} {p q s t : ℝ} (hθ : 0 < paramTheta d p q s t) :
    2 * gammaLoc p q t + 2 * gammaLoc p q t * sigmaUpper d p s / paramTheta d p q s t =
      gammaCacc d p q s t := by
  unfold gammaCacc
  apply (eq_div_iff hθ.ne').mpr
  rw [add_mul, div_mul_cancel₀ _ hθ.ne']
  have : paramTheta d p q s t + sigmaUpper d p s = 1 - sigmaLower d q t := by
    unfold paramTheta sigmaUpper sigmaLower
    ring
  calc _ = 2 * gammaLoc p q t * (paramTheta d p q s t + sigmaUpper d p s) := by ring
    _ = _ := by rw [this]

/-- **Proposition `p.cg.caccioppoli`** from Proposition `p.good.radius.energy` (taken as the
hypothesis `h72` restricted to narrower widths) and Proposition `p.good.radius`. -/
theorem caccioppoli_inequality_of_energy (h72 :

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
            (hv : IsWeightedSubsolution a (originCube 1) v G) →
            ∀ ρ₁ ρ₂ : ℝ, (1 / 2 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
              weightedEnergy a (originCube ρ₁) G ≤
                C * ENNReal.rpow (ENNReal.ofReal (ρ₂ - ρ₁)) (-gammaCacc d p q s t) *
                  upperMoment a ha s p hs (le_of_lt hp) *
                  ENNReal.rpow (contrast a ha s t p q hs ht
                    (le_of_lt hp) (le_of_lt hq))
                    (sigmaUpper d p s / paramTheta d p q s t) *
                  ENNReal.rpow
                    (eLpNorm v 2 (volume.restrict (originCube ρ₂))) 2 := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨C, hC, hsurf⟩ := two_sided_of_energy h72 d hd p q s t hp hq hs ht hθ
  have hdr : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 0 < 20000 * (d : ℝ) := by positivity
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hm : 0 < sigmaUpper d p s := by
    unfold sigmaUpper
    exact add_pos hs (div_pos (by linarith only [hdr]) (by positivity))
  have hθ1 : paramTheta d p q s t < 1 :=
    (Assembly.caccioppoli_parameter_facts hd hp hq hs ht hθ).2.1
  have ht1 : t < 1 := by
    have hc : 0 < (((d : ℝ) - 1) / 2) * (1 / p + 1 / q) := by
      have : 0 < 1 / p + 1 / q := add_pos (one_div_pos.mpr hp0) (one_div_pos.mpr hq0)
      exact mul_pos (by linarith only [hdr]) this
    unfold paramTheta at hθ
    linarith only [hθ, hs, hc]
  have hγ : paramTheta d p q s t ≤ gammaLoc p q t := by
    have h1 : 0 < 1 / (2 * p) := by positivity
    have h2 : 0 < 1 / (2 * q) := by positivity
    unfold gammaLoc
    linarith only [hθ1, ht1, h1, h2]
  obtain ⟨K, hK, hwindow⟩ := Assembly.caccioppoli_finite_window hC.ne hD hθ hγ hm.le
  refine ⟨ENNReal.ofReal (K * (2 : ℝ) ^ (sigmaUpper d p s / paramTheta d p q s t)),
    ENNReal.ofReal_lt_top, ?_⟩
  intro a ha hrange v G hvpos hv ρ R hρ hρR hR
  obtain ⟨hU, hL, hΘ⟩ := Assembly.caccioppoli_moments_finite (ha := ha) hp hq hs ht hrange
  change upperMoment a ha s p hs hp.le < ⊤ at hU
  change 0 < lowerMoment a ha t q ht hq.le at hL
  change contrast a ha s t p q hs ht hp.le hq.le < ⊤ at hΘ
  have hΘ1 : 1 ≤ contrast a ha s t p q hs ht hp.le hq.le :=
    Harnack.Moments.moment_contrast_ge_one (by omega) a ha hs ht hp.le hq.le hU hL
  have hUp := Assembly.two_sided_upper_moment_pos (by omega : 0 < d) a ha hs hp.le
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδ1 : R - ρ ≤ 1 := by linarith only [hρ, hR]
  have hmθ : 0 ≤ sigmaUpper d p s / paramTheta d p q s t := div_nonneg hm.le hθ.le
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hKc : 0 < K * (2 : ℝ) ^ (sigmaUpper d p s / paramTheta d p q s t) := by positivity
  by_cases hN : eLpNorm v 2 (volume.restrict (originCube R)) = ⊤
  · have hcoef : ENNReal.ofReal (K * (2 : ℝ) ^ (sigmaUpper d p s / paramTheta d p q s t)) *
        ENNReal.rpow (ENNReal.ofReal (R - ρ)) (-gammaCacc d p q s t) *
        upperMoment a ha s p hs hp.le *
        ENNReal.rpow (contrast a ha s t p q hs ht hp.le hq.le)
          (sigmaUpper d p s / paramTheta d p q s t) ≠ 0 := by
      have hT : contrast a ha s t p q hs ht hp.le hq.le ≠ 0 :=
        (lt_of_lt_of_le zero_lt_one hΘ1).ne'
      simp only [ENNReal.rpow_eq_pow]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr hKc).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hδ) ENNReal.ofReal_ne_top).ne') hUp.ne')
        (ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hT) hΘ.ne).ne'
    simp only [ENNReal.rpow_eq_pow] at hcoef ⊢
    rw [hN, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.mul_top hcoef]
    exact le_top
  have hb := hwindow (fun r => weightedEnergy a (originCube r) G) ρ R
    (contrast a ha s t p q hs ht hp.le hq.le) (upperMoment a ha s p hs hp.le)
    (eLpNorm v 2 (volume.restrict (originCube R)))
    (Assembly.caccioppoli_energy_mono a G) hρR hδ1
    (Assembly.caccioppoli_energy_finite ha hv hR) hΘ.ne hU.ne hN (by
      intro r z hρr hrz hzR n hn
      have hi := hsurf a ha hrange v G hvpos hv r z (hρ.trans hρr) hrz
        (hzR.trans hR) n hn
      apply hi.trans
      gcongr
      exact Assembly.caccioppoli_cube_mono hzR)
  rw [exponent_identity hθ] at hb
  have hΘr : 1 ≤ (contrast a ha s t p q hs ht hp.le hq.le).toReal := by
    have := ENNReal.toReal_mono hΘ.ne hΘ1
    simpa using this
  have hreal : K * (R - ρ) ^ (-gammaCacc d p q s t) *
      (upperMoment a ha s p hs hp.le).toReal *
      (1 + (contrast a ha s t p q hs ht hp.le hq.le).toReal) ^
        (sigmaUpper d p s / paramTheta d p q s t) *
      (eLpNorm v 2 (volume.restrict (originCube R))).toReal ^ 2 ≤
      (K * (2 : ℝ) ^ (sigmaUpper d p s / paramTheta d p q s t)) *
        (R - ρ) ^ (-gammaCacc d p q s t) *
        (upperMoment a ha s p hs hp.le).toReal *
        (contrast a ha s t p q hs ht hp.le hq.le).toReal ^
          (sigmaUpper d p s / paramTheta d p q s t) *
        (eLpNorm v 2 (volume.restrict (originCube R))).toReal ^ 2 := by
    have h2 : (1 + (contrast a ha s t p q hs ht hp.le hq.le).toReal) ^
        (sigmaUpper d p s / paramTheta d p q s t) ≤
        (2 : ℝ) ^ (sigmaUpper d p s / paramTheta d p q s t) *
          (contrast a ha s t p q hs ht hp.le hq.le).toReal ^
            (sigmaUpper d p s / paramTheta d p q s t) := by
      rw [← Real.mul_rpow (by norm_num) (by linarith only [hΘr])]
      exact Real.rpow_le_rpow (by linarith only [hΘr]) (by linarith only [hΘr]) hmθ
    have hpos : 0 ≤ K * (R - ρ) ^ (-gammaCacc d p q s t) *
        (upperMoment a ha s p hs hp.le).toReal := by positivity
    calc _ ≤ K * (R - ρ) ^ (-gammaCacc d p q s t) *
          (upperMoment a ha s p hs hp.le).toReal *
          ((2 : ℝ) ^ (sigmaUpper d p s / paramTheta d p q s t) *
            (contrast a ha s t p q hs ht hp.le hq.le).toReal ^
              (sigmaUpper d p s / paramTheta d p q s t)) *
          (eLpNorm v 2 (volume.restrict (originCube R))).toReal ^ 2 := by gcongr
      _ = _ := by ring
  have hconv := ofReal_expression_eq (κ := gammaCacc d p q s t) hKc.le hδ hmθ hU.ne hΘ.ne
    (lt_top_iff_ne_top.mpr hN).ne
  refine hb.trans ((ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_))
  rw [hconv]

end CoarseDeGiorgi.CgCaccioppoli
