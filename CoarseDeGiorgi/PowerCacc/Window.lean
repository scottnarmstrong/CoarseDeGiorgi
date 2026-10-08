import CoarseDeGiorgi.Assembly.CaccioppoliWindow
import CoarseDeGiorgi.Assembly.CaccioppoliParameters
import CoarseDeGiorgi.Assembly.LocalBoundedness
import CoarseDeGiorgi.Harnack.Powers.SignedPower
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.PowerFactor
import CoarseDeGiorgi.Statements.GammaLoc
import CoarseDeGiorgi.Statements.SigmaUpper
import CoarseDeGiorgi.Statements.SigmaLower
import CoarseDeGiorgi.Statements.AlphaParam
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Statements.WeightedEnergy

namespace CoarseDeGiorgi.PowerCacc

open Homogenization MeasureTheory
open scoped ENNReal

private lemma powerFactor_pos {m : ℝ} (hm : m < 1 / 2) (hm0 : m ≠ 0) :
    0 < powerFactor m := by
  have hden : 0 < 1 - 2 * m := by linarith
  exact div_pos (abs_pos.mpr hm0) hden

private lemma powerCaccioppoli_exponent_identity {d : ℕ} {p q s t : ℝ}
    (hθ : 0 < paramTheta d p q s t) :
    2 * gammaLoc p q t +
      2 * gammaLoc p q t * (sigmaUpper d p s + sigmaLower d q t - t) /
        paramTheta d p q s t =
      2 * gammaLoc p q t * alphaParam t /
        paramTheta d p q s t := by
  have hsum : paramTheta d p q s t + (sigmaUpper d p s + sigmaLower d q t - t) =
      alphaParam t := by
    unfold paramTheta sigmaUpper sigmaLower alphaParam
    ring
  have htheta : paramTheta d p q s t ≠ 0 := ne_of_gt hθ
  calc
    _ = 2 * gammaLoc p q t *
        (paramTheta d p q s t + (sigmaUpper d p s + sigmaLower d q t - t)) /
          paramTheta d p q s t := by
      field_simp [htheta]
    _ = _ := by rw [hsum]

private lemma ofReal_mul_five {a b c d e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (_he : 0 ≤ e) :
    ENNReal.ofReal (a * b * c * d * e) =
      ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c *
        ENNReal.ofReal d * ENNReal.ofReal e := by
  calc
    ENNReal.ofReal (a * b * c * d * e) =
        ENNReal.ofReal (a * b * c * d) * ENNReal.ofReal e :=
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd)
    _ = (ENNReal.ofReal (a * b * c) * ENNReal.ofReal d) * ENNReal.ofReal e := by
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha hb) hc)]
    _ = ((ENNReal.ofReal (a * b) * ENNReal.ofReal c) * ENNReal.ofReal d) *
        ENNReal.ofReal e := by
      rw [ENNReal.ofReal_mul (mul_nonneg ha hb)]
    _ = ((ENNReal.ofReal a * ENNReal.ofReal b) * ENNReal.ofReal c *
        ENNReal.ofReal d) * ENNReal.ofReal e := by
      rw [ENNReal.ofReal_mul ha]

/-- The source Lʳ one-surface estimate is the sole analytic premise here.  The
fixed-width branches and the complete radius hole filling are discharged by
the existing Caccioppoli window machinery.  The coefficient scales in the
one-surface premise as `c_m` in both terms; writing the scaled moments below
retains exactly `c_m² (1 + c_m² Θ)^(σ/θ)` in the conclusion.
-/
theorem power_caccioppoli_window_of_one_surface
    {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (Csurf : ℝ≥0∞) (hCsurf : Csurf < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε →
            ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
              ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                (∀ ρ' R' : ℝ, ρ ≤ ρ' → ρ' < R' → R' ≤ R →
                  ∀ n : ℤ, (3 : ℝ) ^ n ≤ (R' - ρ') / (20000 * (d : ℝ)) →
                    weightedEnergy a (originCube ρ')
                        (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                      Csurf * (ENNReal.ofReal (R' - ρ')).rpow
                          (-gammaLoc p q t) *
                        (((ENNReal.ofReal (powerFactor m ^ 2) *
                            contrast a ha s t p q hs ht hp.le hq.le).rpow (1 / 2)) *
                            (ENNReal.ofReal ((3 : ℝ) ^ n)).rpow
                              (paramTheta d p q s t) *
                            weightedEnergy a (originCube R')
                              (fun x => (m * (u x + ε) ^ (m - 1)) • G x) +
                          ((ENNReal.ofReal (powerFactor m ^ 2) *
                              upperMoment a ha s p hs hp.le).rpow (1 / 2)) *
                            (ENNReal.ofReal ((3 : ℝ) ^ n)).rpow
                              (-((sigmaUpper d p s + sigmaLower d q t - t))) *
                            eLpNorm (fun x => (u x + ε) ^ m)
                              (ENNReal.ofReal (paramR q))
                              (volume.restrict (originCube R)) *
                            (weightedEnergy a (originCube R')
                              (fun x => (m * (u x + ε) ^ (m - 1)) • G x)).rpow
                                (1 / 2))) →
                weightedEnergy a (originCube ρ)
                    (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                  C * (ENNReal.ofReal (R - ρ)).rpow
                      (-2 * gammaLoc p q t * alphaParam t /
                        paramTheta d p q s t) *
                    upperMoment a ha s p hs hp.le *
                    ENNReal.ofReal (powerFactor m ^ 2) *
                    (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                      contrast a ha s t p q hs ht hp.le hq.le).rpow
                        ((sigmaUpper d p s + sigmaLower d q t - t) / paramTheta d p q s t) *
                    (eLpNorm (fun x => (u x + ε) ^ m)
                      (ENNReal.ofReal (paramR q))
                      (volume.restrict (originCube R))).rpow 2 := by
  have hD : 0 < 20000 * (d : ℝ) := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hd']
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hpq : 0 ≤ ((d : ℝ) - 1) / 2 * (1 / p + 1 / q) :=
    mul_nonneg (div_nonneg hd1 (by norm_num))
      (add_nonneg (one_div_nonneg.mpr hp0.le) (one_div_nonneg.mpr hq0.le))
  have hgamma : paramTheta d p q s t ≤ gammaLoc p q t := by
    unfold paramTheta gammaLoc
    have h1 : 0 ≤ 1 / (2 * p) := by positivity
    have h2 : 0 ≤ 1 / (2 * q) := by positivity
    linarith only [hpq, hs, h1, h2]
  have hsigma : 0 ≤ (sigmaUpper d p s + sigmaLower d q t - t) := by
    unfold sigmaUpper sigmaLower
    have h1 : 0 ≤ ((d : ℝ) - 1) / (2 * p) := by positivity
    have h2 : 0 ≤ ((d : ℝ) - 1) / (2 * q) := by positivity
    linarith only [hs, h1, h2]
  obtain ⟨K, hK, hwindow⟩ := Assembly.caccioppoli_finite_window hCsurf.ne hD hθ
    hgamma hsigma
  refine ⟨ENNReal.ofReal K, ENNReal.ofReal_lt_top, ?_⟩
  intro a ha hrange u G huNonneg hsup ε hε m hm hm0 ρ R hρ hρR hR hsurface
  let cm : ℝ := powerFactor m
  let Θ : ℝ≥0∞ := ENNReal.ofReal (cm ^ 2) *
    contrast a ha s t p q hs ht hp.le hq.le
  let Λ : ℝ≥0∞ := ENNReal.ofReal (cm ^ 2) * upperMoment a ha s p hs hp.le
  let N : ℝ≥0∞ := eLpNorm (fun x => (u x + ε) ^ m)
    (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))
  let H : Vec d → Vec d := fun x => (m * (u x + ε) ^ (m - 1)) • G x
  have hcm : 0 < cm := by
    dsimp [cm]
    exact powerFactor_pos hm hm0
  have hmom := Assembly.caccioppoli_moments_finite hp hq hs ht hrange
  have hΘ : Θ < ⊤ := by
    dsimp [Θ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmom.2.2
  have hΛ : Λ < ⊤ := by
    dsimp [Λ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmom.1
  have hVpair := Assembly.theoremA_unitCube_domain d
  have hNeZero : NeZero d := ⟨by omega⟩
  change IsWeightedSubsolution a (originCube 1)
    (fun x => -u x) (fun x => -G x) at hsup
  have hdoubleNeg := @Weighted.MemH1a.neg d (originCube 1) a hNeZero
    hVpair.1 hVpair.2 ha (fun x => -u x) (fun x => -G x) hsup.1
  have hu : MemH1a a (originCube 1) u G := by
    apply Weighted.MemH1a.congr_ae hdoubleNeg
    · filter_upwards [] with x
      simp
    · filter_upwards [] with x
      simp
  have hr := Assembly.theoremA_paramR_range hq
  have hpower := @Harnack.Powers.signedPower_source_package d hNeZero (originCube 1) a
    hVpair.1 hVpair.2 ha u G hu hsup
    huNonneg ε m (paramR q) hε hm hm0 hr.1 hr.2
  have hN : N < ⊤ := by
    dsimp [N]
    apply lt_of_le_of_lt _ hpower.2.1.eLpNorm_lt_top
    exact eLpNorm_mono_measure _
      (Measure.restrict_mono (Assembly.caccioppoli_cube_mono hR) le_rfl)
  have henergy : weightedEnergy a (originCube R) H < ⊤ := by
    dsimp [H]
    exact (Assembly.caccioppoli_energy_mono a H hR).trans_lt
      (Weighted.MemH1a.energy_lt_top hVpair.1.isOpen ha hpower.1)
  have hδ : 0 < R - ρ := sub_pos.mpr hρR
  have hδ1 : R - ρ ≤ 1 := by linarith only [hρ, hR]
  have hb := hwindow (fun r => weightedEnergy a (originCube r) H) ρ R Θ Λ N
    (Assembly.caccioppoli_energy_mono a H) hρR hδ1 henergy hΘ.ne hΛ.ne hN.ne
    (by
      intro r z hρr hrz hzR n hn
      have hlocal := hsurface r z hρr hrz hzR n hn
      simpa only [Θ, Λ, N, H, cm] using hlocal)
  rw [powerCaccioppoli_exponent_identity hθ] at hb
  have htarget : ENNReal.ofReal
      (K * (R - ρ) ^ (-2 * gammaLoc p q t *
        alphaParam t / paramTheta d p q s t) *
        Λ.toReal * (1 + Θ.toReal) ^
          ((sigmaUpper d p s + sigmaLower d q t - t) / paramTheta d p q s t) * N.toReal ^ 2) =
      ENNReal.ofReal K * (ENNReal.ofReal (R - ρ)).rpow
          (-2 * gammaLoc p q t * alphaParam t /
            paramTheta d p q s t) *
        upperMoment a ha s p hs hp.le * ENNReal.ofReal (cm ^ 2) *
        (1 + ENNReal.ofReal (cm ^ 2) *
          contrast a ha s t p q hs ht hp.le hq.le).rpow
            ((sigmaUpper d p s + sigmaLower d q t - t) / paramTheta d p q s t) *
        N.rpow 2 := by
    have hT : 0 < 1 + Θ.toReal := by positivity
    have hgapPow : ENNReal.ofReal ((R - ρ) ^
        (-2 * gammaLoc p q t * alphaParam t /
          paramTheta d p q s t)) =
        (ENNReal.ofReal (R - ρ)).rpow
          (-2 * gammaLoc p q t * alphaParam t /
            paramTheta d p q s t) :=
      (ENNReal.ofReal_rpow_of_pos hδ).symm
    have hThetaPow : ENNReal.ofReal ((1 + Θ.toReal) ^
        ((sigmaUpper d p s + sigmaLower d q t - t) / paramTheta d p q s t)) =
        (1 + Θ).rpow ((sigmaUpper d p s + sigmaLower d q t - t) / paramTheta d p q s t) := by
      rw [(ENNReal.ofReal_rpow_of_pos hT).symm,
        ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) ENNReal.toReal_nonneg,
        ENNReal.ofReal_one, ENNReal.ofReal_toReal hΘ.ne,
        ENNReal.rpow_eq_pow]
    have hNpow : ENNReal.ofReal (N.toReal ^ 2) = N.rpow 2 := by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg 2, ← ENNReal.rpow_two,
        ENNReal.ofReal_toReal hN.ne, ENNReal.rpow_eq_pow]
    calc
      _ = ENNReal.ofReal K * ENNReal.ofReal ((R - ρ) ^
          (-2 * gammaLoc p q t * alphaParam t /
            paramTheta d p q s t)) * ENNReal.ofReal Λ.toReal *
          ENNReal.ofReal ((1 + Θ.toReal) ^
            ((sigmaUpper d p s + sigmaLower d q t - t) / paramTheta d p q s t)) *
          ENNReal.ofReal (N.toReal ^ 2) :=
        ofReal_mul_five (by positivity) (by positivity) (by positivity)
          (by positivity) (by positivity)
      _ = ENNReal.ofReal K * (ENNReal.ofReal (R - ρ)).rpow
            (-2 * gammaLoc p q t * alphaParam t /
              paramTheta d p q s t) * Λ *
          (1 + Θ).rpow ((sigmaUpper d p s + sigmaLower d q t - t) / paramTheta d p q s t) *
          N.rpow 2 := by
        rw [hgapPow, ENNReal.ofReal_toReal hΛ.ne, hThetaPow, hNpow]
      _ = _ := by
        dsimp [Λ, Θ, N, cm]
        ac_rfl
  rw [show -(2 * gammaLoc p q t * alphaParam t /
      paramTheta d p q s t) =
        -2 * gammaLoc p q t * alphaParam t /
          paramTheta d p q s t by ring] at hb
  rw [htarget] at hb
  exact hb

end CoarseDeGiorgi.PowerCacc
