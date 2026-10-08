import CoarseDeGiorgi.PowerCacc.OneSurfaceMain
import CoarseDeGiorgi.PowerCacc.Window
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.GammaLoc

/-! # Proposition `p.power.caccioppoli` from Lemma `l.exterior.integral`, Proposition
`p.whitney.extension` and the existence of the piecewise harmonic extension

`power_caccioppoli_inequality_of_extension` has the statement of
`CoarseDeGiorgi.power_caccioppoli_inequality`; the three hypotheses give `l.exterior.integral`, `p.whitney.extension` and existence of a piecewise
harmonic extension, restricted to narrower triadic widths. -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.PowerCacc

theorem power_caccioppoli_inequality_of_extension
    (h71 : ExteriorIntegralHyp) (h62 : WhitneyHarmonicExtensionHyp)
    (hex : PiecewiseHarmonicExtensionExistsHyp) :
    ∀ d : ℕ, 3 ≤ d → ∀ p q s t : ℝ,
      (hp : 1 < p) → (hq : 1 < q) → (hs : 0 < s) → (ht : 0 < t) →
      0 < paramTheta d p q s t →
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          spatialMomentRange a ha p q s t →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            ∀ ε : ℝ, 0 < ε →
              ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
                ∀ ρ₁ ρ₂ : ℝ, 1 / 2 ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
                  weightedEnergy a (originCube ρ₁)
                    (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                    C * (ENNReal.ofReal (ρ₂ - ρ₁)).rpow
                        (-2 * gammaLoc p q t * alphaParam t /
                          paramTheta d p q s t) *
                      upperMoment a ha s p hs (le_of_lt hp) *
                      ENNReal.ofReal (powerFactor m ^ 2) *
                      (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                        contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                          ((sigmaUpper d p s + sigmaLower d q t - t) /
                            paramTheta d p q s t) *
                      (eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
                        (volume.restrict (originCube ρ₂))).rpow 2 := by
  intro d hd p q s t hp hq hs ht hθ
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, d = n + 1 := ⟨d - 1, by omega⟩
  obtain ⟨Csurf, hCsurf, hsurface⟩ :=
    power_one_surface_of_extension h71 h62 hex n hd p q s t hp hq hs ht hθ
  obtain ⟨C, hC, hwindow⟩ := power_caccioppoli_window_of_one_surface
    hd hp hq hs ht hθ Csurf hCsurf
  refine ⟨C, hC, ?_⟩
  intro a ha hrange u G hunonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  apply hwindow a ha hrange u G hunonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  intro ρ' R' hρ' hρR' hR' k hwidth
  have hρhalf : 1 / 2 ≤ ρ' := hρ.trans hρ'
  have hRone : R' ≤ 1 := hR'.trans hR
  have hdim : (3 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hd
  have hden : 1 ≤ 20000 * ((n + 1 : ℕ) : ℝ) := by linarith only [hdim]
  have hgap : R' - ρ' ≤ 1 := by linarith only [hρhalf, hRone]
  have hwidthOne : (3 : ℝ) ^ k ≤ 1 := hwidth.trans
    ((div_le_one (by linarith only [hden])).mpr (hgap.trans hden))
  have htri := Harnack.PowerCaccioppoli.triadic_width_of_zpow_le_one hwidthOne
  have hone := hsurface a ha hrange u G hunonneg hsup ε hε m hm hm0
    ρ' R' hρhalf hρR' hRone ((3 : ℝ) ^ k) htri (zpow_pos (by norm_num) _) hwidth
  apply hone.trans
  gcongr
  exact Assembly.caccioppoli_cube_mono hR'

end CoarseDeGiorgi.PowerCacc
