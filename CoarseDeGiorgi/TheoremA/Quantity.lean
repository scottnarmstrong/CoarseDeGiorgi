module

public import CoarseDeGiorgi.Assembly.LocalBoundedness
public import CoarseDeGiorgi.Statements.SigmaUpper
public import CoarseDeGiorgi.Statements.SigmaLower
public import CoarseDeGiorgi.Statements.GammaCacc
public import CoarseDeGiorgi.Statements.GammaSup
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.WeightedEnergy
public import CoarseDeGiorgi.Statements.TwoLevelQuantity
public import CoarseDeGiorgi.Statements.SpatialMomentRange
public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta

/-! The initial estimate of the two-level quantity from the Caccioppoli inequality (Proposition
`p.cg.caccioppoli`): the power of the contrast is `Θ ^ ((1 - σ_*) / (2θ))`, obtained from
`Θ · Θ ^ (σ / θ) = Θ ^ ((1 - σ_*) / θ)`, which holds because `θ = 1 - σ - σ_*`. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.TheoremA

/-- `θ = 1 - σ - σ_*`. -/
theorem paramTheta_eq {d : ℕ} {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) :
    paramTheta d p q s t = 1 - sigmaUpper d p s - sigmaLower d q t := by
  have hp0 : p ≠ 0 := by positivity
  have hq0 : q ≠ 0 := by positivity
  unfold paramTheta sigmaUpper sigmaLower
  field_simp
  ring

/-- Caccioppoli (Proposition `p.cg.caccioppoli`) initializes the zero-level quantity. -/
theorem quantity_of_caccioppoli {d : ℕ} {a : CoeffField d}
    {ha : IsWeightedCoeffOn (originCube 1) a} {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) {u : Vec d → ℝ} {G : Vec d → Vec d}
    {C D : ENNReal} {κ : ℝ} {ρ R : ℝ} (hρR : ρ ≤ R) (hR : R ≤ 1) (hκ : 0 ≤ κ)
    (hσ : 1 - sigmaLower d q t = paramTheta d p q s t + sigmaUpper d p s)
    (hA : 0 ≤ 1 - sigmaLower d q t)
    (hΘ1 : 1 ≤ contrast a ha s t p q hs ht hp.le hq.le)
    (hΘ : contrast a ha s t p q hs ht hp.le hq.le < ⊤)
    (hu : AEStronglyMeasurable (positivePart u) (volume.restrict (originCube ρ)))
    (hD : D ≤ 1)
    (hE : weightedEnergy a (originCube ρ) ({x | 0 < u x}.indicator G) ≤
      C * D ^ (-κ) * upperMoment a ha s p hs hp.le *
        (contrast a ha s t p q hs ht hp.le hq.le) ^
          (sigmaUpper d p s / paramTheta d p q s t) *
        eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) ^ (2 : ℝ)) :
    twoLevelQuantity a ha q t ht hq.le u G 0 ρ ≤
      (1 + C) ^ (1 / 2 : ℝ) * D ^ (-κ / 2) *
        (contrast a ha s t p q hs ht hp.le hq.le) ^
          ((1 - sigmaLower d q t) / (2 * paramTheta d p q s t)) *
        eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) := by
  let B := contrast a ha s t p q hs ht hp.le hq.le
  let m := sigmaUpper d p s / paramTheta d p q s t
  have hB0 : B ≠ 0 := (lt_of_lt_of_le zero_lt_one hΘ1).ne'
  have hBt : B ≠ ⊤ := hΘ.ne
  have hid : 1 + m = (1 - sigmaLower d q t) / paramTheta d p q s t := by
    dsimp only [m]
    apply (eq_div_iff hθ.ne').mpr
    rw [add_mul, div_mul_cancel₀ _ hθ.ne', hσ]
    ring
  have he : 0 ≤ (1 - sigmaLower d q t) / paramTheta d p q s t := div_nonneg hA hθ.le
  have hQ : (lowerMoment a ha t q ht hq.le)⁻¹ *
      weightedEnergy a (originCube ρ) ({x | 0 < u x}.indicator G) ≤
      C * D ^ (-κ) * B ^ ((1 - sigmaLower d q t) / paramTheta d p q s t) *
        eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) ^ (2 : ℝ) := by
    calc
      _ ≤ (lowerMoment a ha t q ht hq.le)⁻¹ * _ := mul_le_mul' le_rfl hE
      _ = C * D ^ (-κ) * (B * B ^ m) *
          eLpNorm (positivePart u) 2 (volume.restrict (originCube R)) ^ (2 : ℝ) := by
        dsimp only [B, contrast]
        rw [div_eq_mul_inv]
        ring
      _ = _ := by
        have hpow := ENNReal.rpow_add 1 m hB0 hBt
        rw [ENNReal.rpow_one] at hpow
        rw [← hpow, hid]
  rw [Assembly.theoremA_twoLevel_zero]
  have hb := Assembly.theoremA_initial_bound hD hΘ1 hκ he
    (Assembly.theoremA_lr_le_l2 hq hρR hR hu) hQ
  have hh : ((1 - sigmaLower d q t) / paramTheta d p q s t) / 2 =
      (1 - sigmaLower d q t) / (2 * paramTheta d p q s t) := by ring
  rw [hh] at hb
  exact hb

end CoarseDeGiorgi.TheoremA
