import CoarseDeGiorgi.Statements.Contrast
import CoarseDeGiorgi.Statements.ParamTheta
import CoarseDeGiorgi.Statements.IsWeightedSupersolution
import CoarseDeGiorgi.Statements.NormalizedLpMoment
import CoarseDeGiorgi.Statements.NonnegativeEssInf
import CoarseDeGiorgi.Statements.HarnackEtaParam
import CoarseDeGiorgi.Statements.CrossoverEstimate
import CoarseDeGiorgi.PowerCacc.HarnackForm
import CoarseDeGiorgi.Harnack.Final.CrossoverAverage
import CoarseDeGiorgi.Harnack.CrossoverFinal.PowerIntegrability
import CoarseDeGiorgi.Harnack.Iterations.UniformThreeIterations
import CoarseDeGiorgi.Harnack.WeakHarnack.CrossoverAssembly
import CoarseDeGiorgi.Harnack.Calculus.Moments
import CoarseDeGiorgi.Harnack.Iterations.MomentNormalization
import Mathlib.Tactic

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Harnack.Final

private theorem originCube_subset_of_radii_local {d : ℕ} {r R : ℝ}
    (hrR : r ≤ R) : originCube (d := d) r ⊆ originCube R := by
  intro x hx i
  dsimp [originCube] at hx ⊢
  constructor <;> linarith [hx i]

private theorem normalizedLpMoment_pos_of_ae_ne_zero {d : ℕ}
    (V : Set (Vec d)) (f : Vec d → ℝ) {p : ℝ} (hp : 0 < p)
    (hVpos : 0 < volume V) (hVtop : volume V < ⊤)
    (hf : AEStronglyMeasurable f (volume.restrict V))
    (hfne : ∀ᵐ x ∂(volume.restrict V), f x ≠ 0) :
    0 < normalizedLpMoment p hp V f := by
  rw [Harnack.Iterations.normalizedLpMoment_eq_eLpNorm V f hp hf]
  apply ENNReal.mul_pos
  · exact (ENNReal.rpow_pos hVpos hVtop.ne).ne'
  · have hne : eLpNorm f (ENNReal.ofReal p) (volume.restrict V) ≠ 0 := by
      intro hz
      have hzero := (eLpNorm_eq_zero_iff (ENNReal.ofReal_pos.mpr hp).ne').mp hz
      have hμ : volume.restrict V ≠ 0 := by
        intro hzeroMeasure
        apply (ne_of_gt hVpos)
        simpa using congrArg (fun μ : Measure (Vec d) => μ Set.univ) hzeroMeasure
      let : (ae (volume.restrict V)).NeBot := ae_neBot.2 hμ
      obtain ⟨x, hx⟩ := (hfne.and hzero).exists
      exact hx.1 hx.2
    exact hne

private theorem normalizedLpMoment_lt_top_of_inverse_power_integrable {d : ℕ}
    (V : Set (Vec d)) (u : Vec d → ℝ) (ε p : ℝ) (hp : 0 < p)
    (hVpos : 0 < volume V)
    (hshift : ∀ᵐ x ∂(volume.restrict V), 0 < u x + ε)
    (hpow : IntegrableOn (fun x => (u x + ε) ^ (-p)) V) :
    normalizedLpMoment p hp V (fun x => (u x + ε)⁻¹) < ⊤ := by
  let f : Vec d → ℝ := fun x => (u x + ε)⁻¹
  let w : Vec d → ℝ := fun x => (u x + ε) ^ (-p)
  have hpowV : Integrable w (volume.restrict V) := hpow
  have hnonneg : 0 ≤ᵐ[volume.restrict V] w := by
    filter_upwards [hshift] with x hx
    dsimp [w]
    exact (Real.rpow_pos_of_pos hx (-p)).le
  have hlinEq :
      (∫⁻ x in V, (ENNReal.ofReal |f x|).rpow p) =
        ∫⁻ x in V, ENNReal.ofReal (w x) := by
    apply lintegral_congr_ae
    filter_upwards [hshift] with x hx
    dsimp [f, w]
    have hpoint : ((u x + ε)⁻¹) ^ p = (u x + ε) ^ (-p) := by
      rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le]
    rw [abs_of_pos (inv_pos.mpr hx)]
    rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr hx)]
    rw [hpoint]
  have hrealLin :
      ENNReal.ofReal (∫ x in V, w x) = ∫⁻ x in V, ENNReal.ofReal (w x) :=
    ofReal_integral_eq_lintegral_ofReal hpowV hnonneg
  have hlinTop : (∫⁻ x in V, (ENNReal.ofReal |f x|).rpow p) < ⊤ := by
    rw [hlinEq, ← hrealLin]
    exact ENNReal.ofReal_lt_top
  have hinvTop : (volume V)⁻¹ < ⊤ := ENNReal.inv_lt_top.mpr
    hVpos
  have hmassTop :
      (volume V)⁻¹ * ∫⁻ x in V, (ENNReal.ofReal |f x|).rpow p < ⊤ :=
    ENNReal.mul_lt_top hinvTop hlinTop
  unfold normalizedLpMoment
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hmassTop.ne

private theorem weakIterationInput_of_powerCaccioppoli
    (hPower : Harnack.Log.powerCaccioppoliInputContract)
    {d : ℕ} (hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) :
    ∀ (c : ℝ), 0 < c →
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
                    ENNReal.ofReal (Real.exp (Kiter / pC)) * Mp := by
  obtain ⟨C₃, γ₆, hC₃, hγ₆, hAll⟩ :=
    Harnack.Iterations.uniform_three_iterations_of_power_caccioppoli
      hPower hd hp hq hs ht hθ
  let Kiter : ℝ := C₃ * (8 : ℝ) ^ γ₆
  have hKiter : 0 ≤ Kiter := by
    dsimp [Kiter]
    exact mul_nonneg (le_trans (by norm_num) hC₃) (Real.rpow_nonneg (by norm_num) _)
  intro c hc hcRange
  refine ⟨Kiter, hKiter, ?_⟩
  intro a ha hUpper hLower _hContrast u G hnonneg hsup ε hε hε1 pC hpC
  let V₃ := originCube (d := d) (3 / 4)
  let V₇ := originCube (d := d) (7 / 8)
  have hrange : spatialMomentRange a ha p q s t :=
    ⟨hp.le, hq.le, hs, ht, hp, hq, hs, ht, hθ, hUpper, hLower⟩
  have hthree := hAll c hc hcRange a ha hrange u G hsup hnonneg ε hε
  dsimp only at hthree
  rcases hthree with ⟨_, hendpoints, _⟩
  obtain ⟨_, hminusInt⟩ :=
    Harnack.CrossoverFinal.shifted_signed_powers_integrable_of_supersolution
      hd p q s t hp hq hs ht hθ a ha hrange c hc hcRange u G hnonneg hsup ε hε
  have hV₇subset : V₇ ⊆ originCube (d := d) 1 :=
    originCube_subset_of_radii_local (by norm_num)
  have hV₃subset : V₃ ⊆ V₇ := originCube_subset_of_radii_local (by norm_num)
  have hV₃subsetUnit : V₃ ⊆ originCube (d := d) 1 := hV₃subset.trans hV₇subset
  have hnonneg₃ : 0 ≤ᵐ[volume.restrict V₃] u :=
    ae_restrict_of_ae_restrict_of_subset hV₃subsetUnit hnonneg
  have hshiftPos : ∀ᵐ x ∂(volume.restrict V₃), 0 < u x + ε := by
    filter_upwards [hnonneg₃] with x hx
    exact add_pos_of_nonneg_of_pos hx hε
  have hminusV : IntegrableOn (fun x => (u x + ε) ^ (-pC)) V₃ :=
    hminusInt.mono_set hV₃subset
  let f : Vec d → ℝ := fun x => (u x + ε)⁻¹
  have hfmeas : AEStronglyMeasurable f (volume.restrict V₃) := by
    have huMeas : AEStronglyMeasurable u (volume.restrict (originCube 1)) := by
      have h := hsup.1.1.neg
      convert h using 1 <;> first | rfl | (funext x; exact (neg_neg (u x)).symm)
    have huMeas₃ : AEStronglyMeasurable u (volume.restrict V₃) :=
      huMeas.mono_measure (Measure.restrict_mono hV₃subsetUnit le_rfl)
    exact (huMeas₃.add aestronglyMeasurable_const).aemeasurable.inv.aestronglyMeasurable
  have hfne : ∀ᵐ x ∂(volume.restrict V₃), f x ≠ 0 := by
    filter_upwards [hshiftPos] with x hx
    dsimp [f]
    exact inv_ne_zero hx.ne'
  have hV₃pos : 0 < volume V₃ := Harnack.Scalar.volume_originCube_pos (by norm_num)
  have hV₃top : volume V₃ < ⊤ :=
    lt_of_le_of_lt (Harnack.Scalar.volume_originCube_le_one (by norm_num)) ENNReal.one_lt_top
  have hMnPos : 0 < normalizedLpMoment pC hpC V₃ f :=
    normalizedLpMoment_pos_of_ae_ne_zero V₃ f hpC hV₃pos hV₃top hfmeas hfne
  have hMnTop : normalizedLpMoment pC hpC V₃ f < ⊤ :=
    normalizedLpMoment_lt_top_of_inverse_power_integrable V₃ u ε pC hpC
      hV₃pos hshiftPos hminusV
  have hKbound (δ : ℝ) (hδ : δ = 1 / 4 ∨ δ = 1 / 8) :
      C₃ * δ ^ (-γ₆) ≤ Kiter := by
    have hpow : δ ^ (-γ₆) ≤ (8 : ℝ) ^ γ₆ := by
      rw [Real.rpow_neg_eq_inv_rpow]
      rcases hδ with hδ | hδ
      · rw [hδ]
        norm_num
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) hγ₆.le
      · rw [hδ]
        norm_num
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hEndpointFactor (δ : ℝ) (hδ : δ = 1 / 4 ∨ δ = 1 / 8) :
      (ENNReal.ofReal (C₃ * δ ^ (-γ₆))) ^ (1 / pC) ≤
        ENNReal.ofReal (Real.exp (Kiter / pC)) := by
    have hδpos : 0 < δ := by
      rcases hδ with hδ | hδ <;> rw [hδ] <;> norm_num
    have hApos : 0 ≤ C₃ * δ ^ (-γ₆) :=
      mul_nonneg (le_trans (by norm_num) hC₃) (Real.rpow_nonneg hδpos.le _)
    have hAupper : C₃ * δ ^ (-γ₆) ≤ Kiter := hKbound δ hδ
    have hKexp : Kiter ≤ Real.exp Kiter := by
      have := Real.add_one_le_exp Kiter
      linarith
    rw [ENNReal.ofReal_rpow_of_nonneg hApos (by positivity : 0 ≤ 1 / pC)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (C₃ * δ ^ (-γ₆)) ^ (1 / pC) ≤ (Real.exp Kiter) ^ (1 / pC) :=
        Real.rpow_le_rpow hApos (hAupper.trans hKexp) (by positivity)
      _ = Real.exp (Kiter / pC) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos Kiter)]
        simp
        ring
  have hfirst := hendpoints (ρ := (1 / 2 : ℝ)) (R := (3 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hsecond := hendpoints (ρ := (5 / 8 : ℝ)) (R := (3 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have hneg :
      (normalizedLpMoment pC hpC V₃ f)⁻¹ ≤
        ENNReal.ofReal (Real.exp (Kiter / pC)) *
          nonnegativeEssInf (originCube (1 / 2)) (fun x => u x + ε) := by
    have hδ : (3 / 4 : ℝ) - (1 / 2 : ℝ) = 1 / 4 := by norm_num
    have hfactor := hEndpointFactor ((3 / 4 : ℝ) - (1 / 2 : ℝ)) (Or.inl hδ)
    simpa [V₃, f, pC] using hfirst.1.trans
      (mul_le_mul_of_nonneg_right hfactor (by positivity))
  have hpositive :
      normalizedLpMoment (harnackEtaParam q) (by
        dsimp [harnackEtaParam, paramR]
        positivity) (originCube (5 / 8)) (fun x => u x + ε) ≤
        ENNReal.ofReal (Real.exp (Kiter / pC)) *
          normalizedLpMoment pC hpC V₃ (fun x => u x + ε) := by
    have hδ : (3 / 4 : ℝ) - (5 / 8 : ℝ) = 1 / 8 := by norm_num
    have hfactor := hEndpointFactor ((3 / 4 : ℝ) - (5 / 8 : ℝ)) (Or.inr hδ)
    simpa [V₃, pC, harnackEtaParam] using hsecond.2.trans
      (mul_le_mul_of_nonneg_right hfactor (by positivity))
  exact ⟨hMnPos, hMnTop, hneg, hpositive⟩

end CoarseDeGiorgi.Harnack.Final

open CoarseDeGiorgi.Harnack.Final

namespace CoarseDeGiorgi

theorem weak_harnack_proved :
    ∀ (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
      (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
      (_hθ : 0 < paramTheta d p q s t),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a),
          upperMoment a ha s p hs hp.le < ⊤ →
          0 < lowerMoment a ha t q ht hq.le →
          ∀ (u : Vec d → ℝ) (G : Vec d → Vec d),
            (∀ᵐ x ∂(volume.restrict (originCube 1)), 0 ≤ u x) →
            IsWeightedSupersolution a (originCube 1) u G →
            normalizedLpMoment (harnackEtaParam q) (by
                have _hq0 : 0 < q := lt_trans (by norm_num) hq
                dsimp [harnackEtaParam, paramR]
                positivity)
              (originCube (5 / 8)) u ≤
              ENNReal.ofReal (Real.exp
                (C * Real.sqrt (contrast a ha s t p q hs ht hp.le hq.le).toReal)) *
                nonnegativeEssInf (originCube (1 / 2)) u := by
  intro d hd p q s t hp hq hs ht hθ
  have hPower : Harnack.Log.powerCaccioppoliInputContract := CoarseDeGiorgi.power_caccioppoli_of_inequality
  exact Harnack.WeakHarnack.weak_harnack_of_crossover_average_and_iterations
    (d := d) hd p q s t hp hq hs ht hθ
    (Harnack.Final.crossover_average_of_statement_crossover
      CoarseDeGiorgi.crossover_estimate hd p q s t hp hq hs ht hθ)
    (fun c hc hcRange a ha hrange u G hsup hnonneg ε hε =>
      Harnack.CrossoverFinal.shifted_signed_powers_integrable_of_supersolution
        hd p q s t hp hq hs ht hθ a ha hrange c hc hcRange u G hnonneg hsup ε hε)
    (Harnack.Final.weakIterationInput_of_powerCaccioppoli
      hPower hd p q s t hp hq hs ht hθ)

end CoarseDeGiorgi
