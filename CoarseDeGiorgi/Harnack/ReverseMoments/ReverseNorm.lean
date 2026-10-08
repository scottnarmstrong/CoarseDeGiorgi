import CoarseDeGiorgi.Harnack.ReverseMoments.CaccioppoliSubstitution
import CoarseDeGiorgi.Assembly.CaccioppoliEnergy
import CoarseDeGiorgi.Statements.ChiParam

namespace CoarseDeGiorgi.Harnack.ReverseMoments

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

/-- The one-step reverse norm estimate. The full power-Caccioppoli
contract is supplied as an explicit input; localization and the bulk embedding
are proved from the lower fractional estimate `lower_fractional_bound`. -/
theorem signed_power_reverse_norm_of_power_caccioppoli
    (hPowerCaccioppoli :
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
                  ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                    weightedEnergy a (originCube ρ)
                      (fun x => (m * (u x + ε) ^ (m - 1)) • G x) ≤
                      C * (ENNReal.ofReal (R - ρ)).rpow
                          (-2 * gammaTwoParam (d := d) p q t * alphaParam t /
                            paramTheta d p q s t) *
                        upperMoment a ha s p hs (le_of_lt hp) *
                        ENNReal.ofReal (powerFactor m ^ 2) *
                        (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                          contrast a ha s t p q hs ht (le_of_lt hp) (le_of_lt hq)).rpow
                          (sigmaParam (d := d) p q s / paramTheta d p q s t) *
                        (eLpNorm (fun x => (u x + ε) ^ m)
                          (ENNReal.ofReal (paramR q))
                          (volume.restrict (originCube R))).rpow 2)
    {d : ℕ} (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε →
            ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
              ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
                eLpNorm (fun x => (u x + ε) ^ m)
                    (ENNReal.ofReal (rStarParam (d := d) q t))
                    (volume.restrict (originCube ρ)) ≤
                  C * ENNReal.ofReal (((R - ρ) / 2) ^
                      (-(gammaOneParam (d := d) q t +
                        gammaTwoParam (d := d) p q t * alphaParam t /
                          paramTheta d p q s t))) *
                    (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                      contrast a ha s t p q hs ht hp.le hq.le).rpow
                      (alphaParam t /
                        (2 * paramTheta d p q s t)) *
                    eLpNorm (fun x => (u x + ε) ^ m)
                      (ENNReal.ofReal (paramR q))
                      (volume.restrict (originCube R)) := by
  obtain ⟨C₀, C₁, hC₀, hC₀top, hC₁top, hstep⟩ :=
    signed_power_inner_bound_of_power_caccioppoli
      hPowerCaccioppoli hd hp hq hs ht hθ
  let C := C₀ * (1 + C₁ ^ (1 / 2 : ℝ))
  have hC₁halfTop : C₁ ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC₁top.ne
  have hC₁halfNonneg : 0 < 1 + C₁ ^ (1 / 2 : ℝ) := by positivity
  have hC₁sumTop : 1 + C₁ ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨by simp, hC₁halfTop⟩
  have hCpos : 0 < C := ENNReal.mul_pos hC₀.ne' hC₁halfNonneg.ne'
  have hCtop : C < ⊤ := ENNReal.mul_lt_top hC₀top hC₁sumTop
  refine ⟨C, hCpos, hCtop, ?_⟩
  intro a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  have hmoment := Assembly.caccioppoli_moments_finite hp hq hs ht hrange
  let θ : ℝ≥0∞ := contrast a ha s t p q hs ht hp.le hq.le
  let F : ℝ≥0∞ := ENNReal.ofReal (powerFactor m ^ 2)
  let X : ℝ≥0∞ := 1 + F * θ
  let gap : ℝ := (R - ρ) / 2
  let b : ℝ := gammaTwoParam (d := d) p q t * alphaParam t /
    paramTheta d p q s t
  let η : ℝ := alphaParam t / (2 * paramTheta d p q s t)
  have hθtop : θ < ⊤ := by simpa only [θ] using hmoment.2.2
  have hθnonneg : 0 ≤ θ := bot_le
  have hFtop : F < ⊤ := by simp [F]
  have hXone : 1 ≤ X := by dsimp [X]; exact le_add_right le_rfl
  have hXtop : X < ⊤ := by
    dsimp [X]
    exact ENNReal.add_lt_top.mpr ⟨by simp, ENNReal.mul_lt_top hFtop hθtop⟩
  have hXzero : X ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hXone)
  have hXtopNe : X ≠ ⊤ := hXtop.ne
  have hgapPos : 0 < gap := by dsimp [gap]; linarith
  have hgapOne : gap ≤ 1 := by dsimp [gap]; linarith
  have hα : 0 < alphaParam t :=
    (Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ).1
  have hσ : 0 < sigmaParam (d := d) p q s := by
    unfold sigmaParam
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    positivity
  have hγ2 : 0 < gammaTwoParam (d := d) p q t := by
    have hγ1 : 0 < gammaOneParam (d := d) q t :=
      lt_of_lt_of_le hα (le_max_left _ _)
    unfold gammaTwoParam
    positivity
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (mul_pos hγ2 hα) hθ
  have hη : 0 < η := by dsimp [η]; positivity
  have hαid : alphaParam t = sigmaParam (d := d) p q s + paramTheta d p q s t := by
    unfold alphaParam sigmaParam paramTheta
    ring_nf
  have hExp : 1 / 2 + sigmaParam (d := d) p q s /
      (2 * paramTheta d p q s t) = η := by
    dsimp [η]
    rw [hαid]
    field_simp [hθ.ne']
    ring
  have hXeta : 1 ≤ X ^ η := ENNReal.one_le_rpow hXone hη
  have hgapb : 1 ≤ gap ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hgapPos hgapOne (by linarith)
  have hgapbE : 1 ≤ ENNReal.ofReal (gap ^ (-b)) :=
    ENNReal.one_le_ofReal.mpr hgapb
  have hgapSmall : 0 < R - ρ := sub_pos.mpr hρR
  have hpowFactor0 : 0 ≤ powerFactor m := by
    unfold powerFactor
    apply div_nonneg (abs_nonneg _)
    linarith
  have hcontrastDef : θ = contrast a ha s t p q hs ht hp.le hq.le := rfl
  have hstep' := hstep a ha hrange u G hnonneg hsup ε hε m hm hm0 ρ R hρ hρR hR
  let H : ℝ≥0∞ := C₁ * (ENNReal.ofReal gap).rpow
      (-2 * gammaTwoParam (d := d) p q t * alphaParam t /
        paramTheta d p q s t) *
      upperMoment a ha s p hs hp.le * F *
      (1 + F * θ).rpow
        (sigmaParam (d := d) p q s / paramTheta d p q s t) *
      (eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
        (volume.restrict (originCube R))).rpow 2
  have hstepExact : eLpNorm (fun x => (u x + ε) ^ m)
        (ENNReal.ofReal (rStarParam (d := d) q t))
        (volume.restrict (originCube ρ)) ≤
      C₀ * ENNReal.ofReal (gap ^ (-gammaOneParam (d := d) q t)) *
        ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) +
          eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
            (volume.restrict (originCube R))) := by
    simpa only [H, gap, F, θ, show ((R - ρ) / 2) = gap by rfl] using hstep'
  have hHroot : H ^ (1 / 2 : ℝ) =
      C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) *
        (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) *
        F ^ (1 / 2 : ℝ) *
        X ^ (sigmaParam (d := d) p q s / (2 * paramTheta d p q s t)) *
        eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
          (volume.restrict (originCube R)) := by
    dsimp [H, b, X]
    simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    rw [show (-2 * gammaTwoParam (d := d) p q t * alphaParam t /
        paramTheta d p q s t) * (1 / 2 : ℝ) = -b by dsimp [b]; ring,
      show (sigmaParam (d := d) p q s / paramTheta d p q s t) *
          (1 / 2 : ℝ) = sigmaParam (d := d) p q s /
            (2 * paramTheta d p q s t) by field_simp,
      show (2 : ℝ) * (1 / 2 : ℝ) = 1 by norm_num, ENNReal.rpow_one]
  have hUL :
      (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
          (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) =
        θ ^ (1 / 2 : ℝ) := by
    have hratio :
        (upperMoment a ha s p hs hp.le / lowerMoment a ha t q ht hq.le) ^
            (1 / 2 : ℝ) =
          upperMoment a ha s p hs hp.le ^ (1 / 2 : ℝ) *
            lowerMoment a ha t q ht hq.le ^ (-1 / 2 : ℝ) := by
      rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), div_eq_mul_inv]
      congr 1
      simpa only [neg_div] using
        (ENNReal.rpow_neg (lowerMoment a ha t q ht hq.le) (1 / 2 : ℝ)).symm
    change (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
        (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ) =
      (upperMoment a ha s p hs hp.le / lowerMoment a ha t q ht hq.le) ^
        (1 / 2 : ℝ)
    calc
      _ = upperMoment a ha s p hs hp.le ^ (1 / 2 : ℝ) *
          lowerMoment a ha t q ht hq.le ^ (-1 / 2 : ℝ) := by ac_rfl
      _ = _ := hratio.symm
  have hFtheta : F * θ ≤ X := by
    dsimp [X]
    exact le_add_left le_rfl
  have hFthetaRoot : (F * θ) ^ (1 / 2 : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hFtheta (by norm_num)
  have hpowerAbsorb :
      (F * θ) ^ (1 / 2 : ℝ) * X ^
          (sigmaParam (d := d) p q s / (2 * paramTheta d p q s t)) ≤ X ^ η := by
    calc
      _ ≤ X ^ (1 / 2 : ℝ) * X ^
            (sigmaParam (d := d) p q s / (2 * paramTheta d p q s t)) :=
          mul_le_mul_of_nonneg_right hFthetaRoot (by positivity)
      _ = X ^ η := by
        rw [← ENNReal.rpow_add _ _ hXzero hXtopNe, hExp]
  let L : ℝ≥0∞ := eLpNorm (fun x => (u x + ε) ^ m)
    (ENNReal.ofReal (paramR q)) (volume.restrict (originCube R))
  have hterm :
      (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) ≤
        C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) * X ^ η *
          eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
            (volume.restrict (originCube R)) := by
    rw [hHroot]
    have hrootProd : F ^ (1 / 2 : ℝ) * θ ^ (1 / 2 : ℝ) =
        (F * θ) ^ (1 / 2 : ℝ) :=
      (ENNReal.mul_rpow_of_nonneg F θ (by norm_num : 0 ≤ (1 / 2 : ℝ))).symm
    calc
      _ = C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) *
          ((lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) *
            (upperMoment a ha s p hs hp.le) ^ (1 / 2 : ℝ)) *
          F ^ (1 / 2 : ℝ) *
          X ^ (sigmaParam (d := d) p q s / (2 * paramTheta d p q s t)) * L := by
            dsimp [L]
            ac_rfl
      _ = C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) *
          θ ^ (1 / 2 : ℝ) * F ^ (1 / 2 : ℝ) *
          X ^ (sigmaParam (d := d) p q s / (2 * paramTheta d p q s t)) * L := by
            rw [hUL]
      _ = C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) *
          (F * θ) ^ (1 / 2 : ℝ) *
          X ^ (sigmaParam (d := d) p q s / (2 * paramTheta d p q s t)) * L := by
            calc
              _ = C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) *
                  (F ^ (1 / 2 : ℝ) * θ ^ (1 / 2 : ℝ)) *
                  X ^ (sigmaParam (d := d) p q s / (2 * paramTheta d p q s t)) * L := by
                    ac_rfl
              _ = _ := by rw [hrootProd]
      _ ≤ C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) *
          X ^ η * L := by
            have hnonneg : 0 ≤ C₁ ^ (1 / 2 : ℝ) *
                (ENNReal.ofReal gap).rpow (-b) := by positivity
            have hnonnegL : 0 ≤ L := bot_le
            have hmul := mul_le_mul_of_nonneg_left hpowerAbsorb hnonneg
            have hmul2 := mul_le_mul_of_nonneg_right hmul hnonnegL
            simpa [mul_assoc] using hmul2
  have hparent : C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) * X ^ η * L + L ≤
      (1 + C₁ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal gap).rpow (-b) * X ^ η * L := by
    have hone : 1 ≤ (ENNReal.ofReal gap).rpow (-b) * X ^ η := by
      change 1 ≤ ENNReal.ofReal gap ^ (-b) * X ^ η
      rw [ENNReal.ofReal_rpow_of_pos hgapPos]
      exact hgapbE.trans (le_mul_of_one_le_right' hXeta)
    calc
      _ = C₁ ^ (1 / 2 : ℝ) *
            ((ENNReal.ofReal gap).rpow (-b) * X ^ η * L) + 1 * L := by ring
      _ ≤ C₁ ^ (1 / 2 : ℝ) *
            ((ENNReal.ofReal gap).rpow (-b) * X ^ η * L) +
          ((ENNReal.ofReal gap).rpow (-b) * X ^ η) * L := by
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right hone (by positivity))
      _ = _ := by ring
  have hcombinedRadius :
      ENNReal.ofReal (gap ^ (-gammaOneParam (d := d) q t)) *
          (ENNReal.ofReal gap).rpow (-b) =
        ENNReal.ofReal (gap ^
          (-(gammaOneParam (d := d) q t + b))) := by
    rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hgapPos,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hgapPos.le _)]
    congr 1
    rw [← Real.rpow_add hgapPos]
    ring_nf
  calc
    _ ≤ C₀ * ENNReal.ofReal (gap ^ (-gammaOneParam (d := d) q t)) *
        ((1 + C₁ ^ (1 / 2 : ℝ)) * (ENNReal.ofReal gap).rpow (-b) * X ^ η * L) := by
      have hsum :
          (lowerMoment a ha t q ht hq.le) ^ (-1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) + L ≤
            C₁ ^ (1 / 2 : ℝ) * (ENNReal.ofReal gap).rpow (-b) * X ^ η * L + L :=
        add_le_add hterm le_rfl
      exact hstepExact.trans <| mul_le_mul_of_nonneg_left
        (hsum.trans hparent) (by positivity)
    _ = C₀ * (1 + C₁ ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal (gap ^ (-(gammaOneParam (d := d) q t + b))) * X ^ η *
          eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
            (volume.restrict (originCube R)) := by
      dsimp [L]
      calc
        _ = C₀ * (1 + C₁ ^ (1 / 2 : ℝ)) *
              (ENNReal.ofReal (gap ^ (-gammaOneParam (d := d) q t)) *
                (ENNReal.ofReal gap).rpow (-b)) * X ^ η *
              eLpNorm (fun x => (u x + ε) ^ m) (ENNReal.ofReal (paramR q))
                (volume.restrict (originCube R)) := by
            rw [← ENNReal.rpow_eq_pow (ENNReal.ofReal gap) (-b)]
            ac_rfl
        _ = _ := by rw [hcombinedRadius]
    _ = _ := by
      simp [C, gap, b, X, θ, η, F, ENNReal.rpow_eq_pow]

end

end CoarseDeGiorgi.Harnack.ReverseMoments
