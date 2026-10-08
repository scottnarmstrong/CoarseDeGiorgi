import CoarseDeGiorgi.Statements.IsWeightedCoeffOn
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.ChiParam
import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.CrossoverExponent
import CoarseDeGiorgi.Statements.HarnackEtaParam
import CoarseDeGiorgi.Statements.LowerMoment
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.NormalizedLpMoment
import CoarseDeGiorgi.Statements.OriginCube
import CoarseDeGiorgi.Statements.ParamR
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.SpatialMomentRange
import CoarseDeGiorgi.Statements.UpperMoment
import CoarseDeGiorgi.Harnack.Crossover.Normalization
import CoarseDeGiorgi.Harnack.WeakHarnack.CrossoverMomentBridge
import CoarseDeGiorgi.Harnack.WeakHarnack.EpsilonUniform

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.WeakHarnack

private theorem originCube_subset_of_radii_local {d : ℕ} {r R : ℝ}
    (hrR : r ≤ R) : originCube (d := d) r ⊆ originCube R := by
  intro x hx i
  dsimp [originCube] at hx ⊢
  constructor <;> linarith [hx i]

private theorem volumeAverage_congr_ae_local {d : ℕ} {V : Set (Vec d)}
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume.restrict V] g) :
    volumeAverage V f = volumeAverage V g := by
  unfold Homogenization.volumeAverage
  rw [integral_congr_ae hfg]

/-- Assemble the raw real-average crossover output and shifted-power
integrability with the normalized-moment iteration bounds. -/
theorem weak_harnack_of_crossover_average_and_iterations {d : ℕ}
    (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (hcrossover : ∃ c : ℝ, 0 < c ∧
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) ∧
      ∃ Kcross : ℝ, 0 ≤ Kcross ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSupersolution a (originCube 1) u G →
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          ∀ ε : ℝ, 0 < ε →
            let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
            volumeAverage (originCube (3 / 4))
                (fun x => (u x + ε) ^ pC) *
              volumeAverage (originCube (3 / 4))
                (fun x => (u x + ε) ^ (-pC)) ≤ Kcross)
    (hpower : ∀ (c : ℝ), 0 < c →
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) →
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        spatialMomentRange a ha p q s t →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          IsWeightedSupersolution a (originCube 1) u G →
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          ∀ ε : ℝ, 0 < ε →
            let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
            IntegrableOn (fun x => (u x + ε) ^ pC) (originCube (7 / 8)) ∧
              IntegrableOn (fun x => (u x + ε) ^ (-pC))
                (originCube (7 / 8)))
    (hiterations : ∀ (c : ℝ), 0 < c →
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) →
      ∃ Kiter : ℝ, 0 ≤ Kiter ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        1 ≤ contrast a ha s t p q hs ht hp.le hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
            ∀ (hpC : 0 < pC),
              let Mp := normalizedLpMoment pC hpC (originCube (3 / 4))
                (fun x => u x + ε)
              let Mn := normalizedLpMoment pC hpC (originCube (3 / 4))
                (fun x => (u x + ε)⁻¹)
              0 < Mn ∧ Mn < ⊤ ∧
                Mn⁻¹ ≤ ENNReal.ofReal (Real.exp (Kiter / pC)) *
                  nonnegativeEssInf (originCube (1 / 2)) (fun x => u x + ε) ∧
                normalizedLpMoment (harnackEtaParam q) (by
                  dsimp [harnackEtaParam, paramR]
                  positivity)
                  (originCube (5 / 8)) (fun x => u x + ε) ≤
                  ENNReal.ofReal (Real.exp (Kiter / pC)) * Mp) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          normalizedLpMoment (harnackEtaParam q) (by
            dsimp [harnackEtaParam, paramR]
            positivity)
            (originCube (5 / 8)) u ≤
            ENNReal.ofReal (Real.exp (C * Real.sqrt
              (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
              nonnegativeEssInf (originCube (1 / 2)) u := by
  have hcross : ∃ c : ℝ, 0 < c ∧
      c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)) ∧
      ∃ Kcross : ℝ, 0 ≤ Kcross ∧
      ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
        upperMoment a ha s p hs hp.le < ⊤ →
        0 < lowerMoment a ha t q ht hq.le →
        ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
          (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
          IsWeightedSupersolution a (originCube 1) u G →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
            ∀ (hpC : 0 < pC),
              normalizedLpMoment pC hpC (originCube (3 / 4))
                  (fun x => u x + ε) *
                normalizedLpMoment pC hpC (originCube (3 / 4))
                  (fun x => (u x + ε)⁻¹) ≤
                ENNReal.ofReal (Real.exp (Kcross / pC)) := by
    rcases hcrossover with ⟨c, hc, hcRange, Kcross, hKcross, haverage⟩
    refine ⟨c, hc, hcRange, Kcross, hKcross, ?_⟩
    intro a ha hupper hlower u G hnonneg hsuper ε hε hε1
    dsimp only
    intro hpC
    have hrange : spatialMomentRange a ha p q s t := by
      exact ⟨hp.le, hq.le, hs, ht, hp, hq, hs, ht, hθ, hupper, hlower⟩
    have hKexp : Kcross ≤ Real.exp Kcross := by
      nlinarith [Real.add_one_le_exp Kcross]
    have hsmallBig : originCube (d := d) (3 / 4) ⊆ originCube (7 / 8) :=
      originCube_subset_of_radii_local (by norm_num)
    have hsmallUnit : originCube (d := d) (3 / 4) ⊆ originCube (1 : ℝ) :=
      originCube_subset_of_radii_local (by norm_num)
    have hnonnegSmall :
        0 ≤ᵐ[volume.restrict (originCube (d := d) (3 / 4))] u :=
      ae_restrict_of_ae_restrict_of_subset hsmallUnit hnonneg
    have hshiftNonneg :
        0 ≤ᵐ[volume.restrict (originCube (d := d) (3 / 4))]
          (fun x => u x + ε) := by
      filter_upwards [hnonnegSmall] with x hx
      exact add_nonneg hx (le_of_lt hε)
    have hshiftPos : ∀ᵐ x ∂(volume.restrict (originCube (d := d) (3 / 4))),
        0 < u x + ε := by
      filter_upwards [hnonnegSmall] with x hx
      exact add_pos_of_nonneg_of_pos hx hε
    have hinvNonneg :
        0 ≤ᵐ[volume.restrict (originCube (d := d) (3 / 4))]
          (fun x => (u x + ε)⁻¹) := by
      filter_upwards [hshiftPos] with x hx
      exact inv_nonneg.mpr hx.le
    have hsourcePower := hpower c hc hcRange a ha hrange u G hsuper hnonneg ε hε
    dsimp only at hsourcePower
    rcases hsourcePower with ⟨hplusInt, hminusInt⟩
    have hplusSmall :
        IntegrableOn (fun x => (u x + ε) ^ crossoverExponent c a ha s t p q hs ht hp.le hq.le)
          (originCube (d := d) (3 / 4)) :=
      hplusInt.mono_set hsmallBig
    have hminusSmall :
        IntegrableOn (fun x => (u x + ε) ^ (-crossoverExponent c a ha s t p q hs ht hp.le hq.le))
          (originCube (d := d) (3 / 4)) :=
      hminusInt.mono_set hsmallBig
    have hinvPowerEq :
        (fun x => (u x + ε)⁻¹ ^ crossoverExponent c a ha s t p q hs ht hp.le hq.le) =ᵐ[
          volume.restrict (originCube (d := d) (3 / 4))]
          (fun x => (u x + ε) ^ (-crossoverExponent c a ha s t p q hs ht hp.le hq.le)) := by
      filter_upwards [hshiftPos] with x hx
      rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
    have hinvAverageEq :
        volumeAverage (originCube (d := d) (3 / 4))
          (fun x => (u x + ε) ^ (-crossoverExponent c a ha s t p q hs ht hp.le hq.le)) =
        volumeAverage (originCube (d := d) (3 / 4))
          (fun x => (u x + ε)⁻¹ ^ crossoverExponent c a ha s t p q hs ht hp.le hq.le) :=
      volumeAverage_congr_ae_local hinvPowerEq.symm
    have haverageBound :
        volumeAverage (originCube (d := d) (3 / 4))
            (fun x => (u x + ε) ^ crossoverExponent c a ha s t p q hs ht hp.le hq.le) *
          volumeAverage (originCube (d := d) (3 / 4))
            (fun x => (u x + ε)⁻¹ ^ crossoverExponent c a ha s t p q hs ht hp.le hq.le) ≤
          Real.exp Kcross := by
      rw [← hinvAverageEq]
      exact (haverage a ha hrange u G hsuper hnonneg ε hε).trans hKexp
    have hinvInt :
        IntegrableOn
          (fun x => (u x + ε)⁻¹ ^ crossoverExponent c a ha s t p q hs ht hp.le hq.le)
          (originCube (d := d) (3 / 4)) :=
      hminusSmall.congr_fun_ae hinvPowerEq.symm
    have hnormalized := normalized_crossover_product_bound
      (originCube (d := d) (3 / 4)) (fun x => u x + ε) (fun x => (u x + ε)⁻¹)
      (crossoverExponent c a ha s t p q hs ht hp.le hq.le) Kcross hpC
      (Harnack.Scalar.volume_originCube_pos (by norm_num))
      (lt_of_le_of_lt (Harnack.Scalar.volume_originCube_le_one (by norm_num))
        ENNReal.one_lt_top)
      hshiftNonneg hinvNonneg hplusSmall hinvInt haverageBound
    simpa only [crossoverExponent] using hnormalized
  exact weak_harnack_of_uniform_crossover_and_iterations
    hd p q s t hp hq hs ht hθ hcross hiterations

end CoarseDeGiorgi.Harnack.WeakHarnack
