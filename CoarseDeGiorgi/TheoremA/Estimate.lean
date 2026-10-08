import CoarseDeGiorgi.TheoremA.Quantity
import CoarseDeGiorgi.TheoremA.Props
import CoarseDeGiorgi.Harnack.Moments.MomentComparison
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.IsWeightedCoeffOn

/-! Theorem A from Propositions `p.cg.caccioppoli` and `p.energy.to.sup`: the `L^∞`-`L²` estimate
with the power `Θ ^ ((d-1)/(4θ))`. -/

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.TheoremA

theorem theoremA_of_props (h81 : Prop81) (h83 : Prop83)
    (d : ℕ) (hd : 3 ≤ d) (p q s t : ℝ) (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSubsolution a (originCube 1) u G →
          LocallyBoundedAbove (originCube 1) u ∧
          ∀ ρ R : ℝ, (1 / 2 : ℝ) ≤ ρ → ρ < R → R ≤ 1 →
            eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
              C * (ENNReal.ofReal (R - ρ)).rpow (-γ) *
                (contrast a ha s t p q hs ht hp.le hq.le).rpow
                  (((d : ℝ) - 1) / (4 * paramTheta d p q s t)) *
                eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) ∧
            (R < 1 → eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) < ⊤) := by
  have hd0 : d ≠ 0 := by omega
  let : NeZero d := ⟨hd0⟩
  obtain ⟨C₁, hC₁, henergy⟩ := h81 d hd p q s t hp hq hs ht hθ
  obtain ⟨C₂, hC₂, hsup⟩ := h83 d hd p q s t hp hq hs ht hθ
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hσpos : 0 < sigmaUpper d p s := by
    unfold sigmaUpper
    have : 0 < ((d : ℝ) - 1) / (2 * p) := div_pos (by linarith only [hd3]) (by positivity)
    linarith only [hs, this]
  have hθeq := paramTheta_eq (d := d) (s := s) (t := t) hp hq
  have hσ : 1 - sigmaLower d q t = paramTheta d p q s t + sigmaUpper d p s := by
    linarith only [hθeq]
  have hA : 0 ≤ 1 - sigmaLower d q t := by
    rw [hσ]; linarith only [hθ, hσpos]
  let κ := |gammaCacc d p q s t|
  let γ₄ := gammaSup d p q s t
  let γ' := γ₄ + κ / 2
  let γ := |γ'| + 1
  let b := ((d : ℝ) - 1) / (4 * paramTheta d p q s t)
  have hκ : 0 ≤ κ := abs_nonneg _
  have hγ : 0 < γ := by positivity
  have hγ'γ : -γ ≤ -γ' := by
    have := le_abs_self γ'
    show -(|γ'| + 1) ≤ -γ'
    linarith only [this]
  let C₀ := 1 + C₂ * (1 + C₁) ^ (1 / 2 : ℝ) * (2 : ENNReal) ^ γ'
  have hC₀ : C₀ < ⊤ := by
    dsimp only [C₀]
    have hC₁plus : 1 + C₁ < ⊤ := ENNReal.add_lt_top.mpr ⟨by simp, hC₁⟩
    have hRoot : (1 + C₁) ^ (1 / 2 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hC₁plus.ne
    have hTwo : (2 : ENNReal) ^ γ' < ⊤ :=
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)).lt_top
    exact ENNReal.add_lt_top.mpr
      ⟨by simp, ENNReal.mul_lt_top (ENNReal.mul_lt_top hC₂ hRoot) hTwo⟩
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one (le_add_right le_rfl)
  refine ⟨γ, hγ, C₀, hC₀, ?_⟩
  intro a ha hUpper hLower u G hu
  have hrange : spatialMomentRange a ha p q s t :=
    ⟨hp.le, hq.le, hs, ht, hp, hq, hs, ht, hθ, hUpper, hLower⟩
  have hΘ : contrast a ha s t p q hs ht hp.le hq.le < ⊤ :=
    ENNReal.div_lt_top hUpper.ne hLower.ne'
  have hΘ1 := Harnack.Moments.moment_contrast_ge_one (by omega) a ha hs ht hp.le hq.le
    hUpper hLower
  let B := contrast a ha s t p q hs ht hp.le hq.le
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hΘ1
  have hlocal := (hsup a ha hrange).2 u G hu
  have hmeas : AEStronglyMeasurable (positivePart u) (volume.restrict (originCube 1)) :=
    (continuous_id.max (continuous_const (y := (0 : ℝ)))).comp_aestronglyMeasurable hu.1.1
  have hpos := Weighted.IsWeightedSubsolution.posPart
    (Assembly.theoremA_unitCube_domain d).1 (Assembly.theoremA_unitCube_domain d).2 ha hu
  have hL₂ : ∀ ρ R : ℝ, (1 / 2 : ℝ) ≤ ρ → ρ < R → R ≤ 1 →
      eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
        C₀ * (ENNReal.ofReal (R - ρ)) ^ (-γ) * B ^ b *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) := by
    intro ρ R hρ hρR hR
    by_cases hN : eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) = ⊤
    · have hpD := ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (sub_pos.mpr hρR))
        ENNReal.ofReal_ne_top (p := -γ)
      have hpB := ENNReal.rpow_pos hB hΘ.ne (p := b)
      rw [hN, ENNReal.mul_top
        (ENNReal.mul_pos (ENNReal.mul_pos hC₀pos.ne' hpD.ne').ne' hpB.ne').ne']
      exact le_top
    let R' := (ρ + R) / 2
    have hρR' : ρ < R' := by dsimp only [R']; linarith only [hρR]
    have hR'R : R' < R := by dsimp only [R']; linarith only [hρR]
    have hhalf : (1 / 2 : ℝ) ≤ R' := hρ.trans hρR'.le
    have hmeas' := hmeas.mono_set (Assembly.caccioppoli_cube_mono (hR'R.le.trans hR))
    have hLr := (Assembly.theoremA_lr_le_l2 hq hR'R.le hR hmeas').trans_lt
      (lt_top_iff_ne_top.mpr hN)
    have hfinite := Assembly.theoremA_twoLevel_finite ht hq.le hu hLower (hR'R.le.trans hR) hLr
    have henergy' := henergy a ha hrange (positivePart u) ({x | 0 < u x}.indicator G)
      (Eventually.of_forall fun x => le_max_right (u x) 0) hpos R' R hhalf hR'R hR
    have hgap : R - R' = (R - ρ) / 2 := by dsimp only [R']; ring
    rw [hgap] at henergy'
    have hD : ENNReal.ofReal ((R - ρ) / 2) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith only [hρ, hR])
    have hκle : ENNReal.ofReal ((R - ρ) / 2) ^ (-gammaCacc d p q s t) ≤
        ENNReal.ofReal ((R - ρ) / 2) ^ (-κ) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hD (by
        have := le_abs_self (gammaCacc d p q s t)
        show -κ ≤ -gammaCacc d p q s t
        linarith only [this])
    have henergy'' : weightedEnergy a (originCube R') ({x | 0 < u x}.indicator G) ≤
        C₁ * ENNReal.ofReal ((R - ρ) / 2) ^ (-κ) * upperMoment a ha s p hs hp.le *
          B ^ (sigmaUpper d p s / paramTheta d p q s t) *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) ^ (2 : ℝ) := by
      simp only [ENNReal.rpow_eq_pow] at henergy' hκle
      refine henergy'.trans ?_
      gcongr
    have hY := quantity_of_caccioppoli hp hq hs ht hθ hR'R.le hR hκ hσ hA hΘ1 hΘ hmeas' hD
      henergy''
    have hM := (hsup a ha hrange).1 u G hu ρ R' hρ hρR' (hR'R.le.trans hR) hfinite
    have hgap' : R' - ρ = (R - ρ) / 2 := by dsimp only [R']; ring
    rw [hgap'] at hM
    have hexp : ((d : ℝ) - 3 + 2 * sigmaLower d q t) / (4 * paramTheta d p q s t) =
        ((d : ℝ) - 1 - 2 * (1 - sigmaLower d q t)) / (4 * paramTheta d p q s t) := by
      congr 1; ring
    rw [hexp] at hM
    have hcomb := Assembly.theoremA_combine (sub_pos.mpr hρR) hB hΘ.ne hY hM
    have hcomb' : eLpNorm (positivePart u) ⊤ (volume.restrict (originCube ρ)) ≤
        (C₂ * (1 + C₁) ^ (1 / 2 : ℝ) * (2 : ENNReal) ^ γ') *
          (ENNReal.ofReal (R - ρ)) ^ (-γ') * B ^ ((↑d - 1) / (4 * paramTheta d p q s t)) *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) := hcomb
    refine hcomb'.trans ?_
    have hδ1 : ENNReal.ofReal (R - ρ) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith only [hρ, hR])
    have hδ : (ENNReal.ofReal (R - ρ)) ^ (-γ') ≤ (ENNReal.ofReal (R - ρ)) ^ (-γ) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hγ'γ
    gcongr
    exact le_add_left le_rfl
  refine ⟨hlocal, fun ρ R hρ hρR hR => ⟨hL₂ ρ R hρ hρR hR, fun hRlt => ?_⟩⟩
  exact Assembly.theoremA_inner_norm_finite hu.1.1 hlocal hRlt 2

end CoarseDeGiorgi.TheoremA
