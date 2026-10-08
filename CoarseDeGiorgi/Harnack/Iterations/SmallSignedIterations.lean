import CoarseDeGiorgi.Harnack.Iterations.SmallMomentChain
import CoarseDeGiorgi.Harnack.Iterations.SmallMomentStep
import CoarseDeGiorgi.Harnack.Iterations.SignedMomentStep
import CoarseDeGiorgi.Harnack.Iterations.ExponentRange
import CoarseDeGiorgi.Harnack.Moments.MomentComparison
import CoarseDeGiorgi.Statements.CrossoverExponent
import CoarseDeGiorgi.Statements.ChiParam

open Homogenization MeasureTheory
open scoped ENNReal

namespace CoarseDeGiorgi.Harnack.Iterations

/-- The two all-radii small signed-power estimates, for every admissible
crossover constant `c`. The reverse input is exactly the normalized reverse estimate,
specialized at the coefficient and supersolution data.
-/
theorem small_signed_iterations_of_normalized_reverse {d : ℕ}
    (hd : 3 ≤ d) {p q s t : ℝ}
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t)
    (C : ℝ≥0∞) (hC1 : 1 ≤ C) (hCtop : C < ⊤)
    (c : ℝ) (hc : 0 < c)
    (hcRange : c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)))
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t)
    (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hsup : IsWeightedSupersolution a (originCube 1) u G)
    (hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
    (ε : ℝ) (hε : 0 < ε)
    (hReverse :
      ∀ m : ℝ, m < 1 / 2 → m ≠ 0 →
        ∀ ρ R : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
          let v : Vec d → ℝ := fun x => (u x + ε) ^ m
          (CoarseDeGiorgi.normalizedLpMoment
              (rStarParam (d := d) q t)
              (ReverseMoments.rStarParam_pos_of_harnack_facts hd hp hq hs ht hθ)
              (originCube ρ) v) ^ (paramR q) ≤
            C * (ENNReal.ofReal (((R - ρ) / 2) ^
                (-(gammaOneParam (d := d) q t +
                  gammaTwoParam (d := d) p q t * alphaParam t /
                    paramTheta d p q s t)))) ^ (paramR q) *
              (1 + ENNReal.ofReal (powerFactor m ^ 2) *
                contrast a ha s t p q hs ht hp.le hq.le).rpow
                  (alphaParam t * paramR q /
                    (2 * paramTheta d p q s t)) *
              (CoarseDeGiorgi.normalizedLpMoment (paramR q)
          (ReverseMoments.paramR_pos_of_harnack_facts hd hp hq hs ht hθ)
                (originCube R) v) ^ (paramR q))
    :
    let r := paramR q
    let χ := chiParam d q t
    let γ₅ := gammaOneParam (d := d) q t +
      gammaTwoParam (d := d) p q t * alphaParam t / paramTheta d p q s t
    let β := alphaParam t * r / (2 * paramTheta d p q s t)
    let A := Real.log C.toReal + (γ₅ * r + β) * Real.log 2
    let C₃ := Real.exp (A * (χ / (χ - 1)) +
      γ₅ * r * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2))
    let γ₆ := γ₅ * r * χ / (χ - 1)
    let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
    (∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (fun x => (u x + ε) ^ pC) 1 (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
          eLpNorm (fun x => (u x + ε) ^ pC) (ENNReal.ofReal b)
            (volume.restrict (originCube R))) ∧
    (∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (fun x => (u x + ε) ^ (-pC)) 1 (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
          eLpNorm (fun x => (u x + ε) ^ (-pC)) (ENNReal.ofReal b)
            (volume.restrict (originCube R))) := by
  let r := paramR q
  let χ := chiParam d q t
  let Θ := contrast a ha s t p q hs ht hp.le hq.le
  let γ₅ := gammaOneParam (d := d) q t +
    gammaTwoParam (d := d) p q t * alphaParam t / paramTheta d p q s t
  let β := alphaParam t * r / (2 * paramTheta d p q s t)
  let A := Real.log C.toReal + (γ₅ * r + β) * Real.log 2
  let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
  obtain ⟨hα, _, hr1, _, _, _, _, hrStar⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hr : 0 < r := zero_lt_one.trans hr1
  have hχ : 1 < χ := by
    dsimp [χ, chiParam]
    exact (lt_div_iff₀ hr).2 (by simpa using hrStar)
  have hχpos : 0 < χ := zero_lt_one.trans hχ
  have hγOne : 0 < gammaOneParam (d := d) q t :=
    hα.trans_le (le_max_left _ _)
  have hγTwo : 0 < gammaTwoParam (d := d) p q t := by
    unfold gammaTwoParam
    have hp0 := zero_lt_one.trans hp
    have hq0 := zero_lt_one.trans hq
    positivity
  have hγ : 0 < γ₅ := by dsimp [γ₅]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hCReal : 1 ≤ C.toReal := by simpa using ENNReal.toReal_mono hCtop.ne hC1
  have hA : 0 ≤ A := by
    dsimp [A]
    have hlogC := Real.log_nonneg hCReal
    have hlog2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  have hRange := hrange
  rcases hRange with ⟨_, _, _, _, _, _, _, _, _, hUpper, hLower⟩
  have hΘtop : Θ < ⊤ := by
    dsimp [Θ, contrast]
    exact ENNReal.div_lt_top hUpper.ne hLower.ne'
  have hΘone : 1 ≤ Θ := Moments.moment_contrast_ge_one (by omega) a ha hs ht
    hp.le hq.le hUpper hLower
  have hExponent := ruled_exponent_range_of_moment_comparison hd p q s t hp hq hs ht
    hθ a ha ⟨hΘone, hΘtop⟩ c hc (by simpa [chiParam] using hcRange)
  have hpC : 0 < pC := hExponent.1
  have hpCquarter : pC < r / 4 := hExponent.2.2.1
  have hpCΘ : pC ^ 2 * Θ.toReal ≤ c ^ 2 := hExponent.2.2.2.2.2
  have hcsmall : 2 * c < r := (div_lt_one hr).mp hExponent.2.2.2.1
  have hUpos : ∀ᵐ x ∂volume.restrict (originCube (d := d) 1), 0 < u x + ε := by
    filter_upwards [hnonneg] with x hx
    exact add_pos_of_nonneg_of_pos hx hε
  have humeas : AEStronglyMeasurable u (volume.restrict (originCube 1)) := by
    have h := hsup.1.1.neg
    convert h using 1 <;> first | rfl | (funext x; exact (neg_neg (u x)).symm)
  have hUmeas : AEStronglyMeasurable (fun x => u x + ε)
      (volume.restrict (originCube 1)) := humeas.add aestronglyMeasurable_const
  have run (negative : Bool) :
      let F : Vec d → ℝ := fun x => if negative then (u x + ε)⁻¹ else u x + ε
      let f : Vec d → ℝ := fun x => (F x) ^ pC
      ∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
        eLpNorm f 1 (volume.restrict (originCube ρ)) ≤
          (ENNReal.ofReal (((2 : ℝ) ^ d * Real.exp (A * (χ / (χ - 1)) +
            γ₅ * r * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2))) *
              (R - ρ) ^ (-(γ₅ * r * χ / (χ - 1))))) ^ (1 / b) *
            eLpNorm f (ENNReal.ofReal b) (volume.restrict (originCube R)) := by
    dsimp only
    let F : Vec d → ℝ := fun x => if negative then (u x + ε)⁻¹ else u x + ε
    let f : Vec d → ℝ := fun x => (F x) ^ pC
    have hFpos : ∀ᵐ x ∂volume.restrict (originCube (d := d) 1), 0 < F x := by
      filter_upwards [hUpos] with x hx
      cases negative
      · exact hx
      · exact inv_pos.mpr hx
    have hFmeas : AEStronglyMeasurable F (volume.restrict (originCube 1)) := by
      cases negative
      · exact hUmeas
      · exact hUmeas.aemeasurable.inv.aestronglyMeasurable
    have hfmeas : AEStronglyMeasurable f (volume.restrict (originCube 1)) :=
      hFmeas.aemeasurable.pow_const pC |>.aestronglyMeasurable
    have hsmall : ∀ (v : ℝ) (hv : 0 < v), v < 1 → ∀ ρ R : ℝ,
        1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
      normalizedLpMoment (χ * v) (mul_pos hχpos hv) (originCube ρ) f ^ v ≤
        ENNReal.ofReal (Real.exp (A + γ₅ * r * Real.log (1 / (R - ρ)))) *
          normalizedLpMoment v hv (originCube R) f ^ v := by
      intro v hv hv1 ρ R hρ hρR hR
      let z := if negative then -(pC * v) else pC * v
      have hzshape : z = pC * v ∨ z = -(pC * v) := by
        cases negative <;> simp [z]
      have hbound := small_signed_powerFactor_bound hpC hpCquarter hc.le hr
        Θ.toReal_nonneg hpCΘ hcsmall hv hv1.le hzshape
      have hzabs : |z| = pC * v := by
        cases negative <;> simp [z, abs_of_pos (mul_pos hpC hv)]
      have hz : z ≠ 0 := by
        intro heq
        have h := congrArg abs heq
        rw [hzabs, abs_zero] at h
        exact (mul_pos hpC hv).ne' h
      let K := C * (ENNReal.ofReal (((R - ρ) / 2) ^ (-γ₅))) ^ r *
        (1 + ENNReal.ofReal (powerFactor (z / r) ^ 2) * Θ) ^ β
      have hWhich : (fun x => if 0 < z then u x + ε else (u x + ε)⁻¹) = F := by
        cases negative <;> simp [z, F, mul_pos hpC hv, not_lt_of_ge (mul_pos hpC hv).le]
      have hSigned := signed_moment_step_of_normalized_reverse hd hp hq hs ht hθ
        C hC1 hCtop a ha hrange u G hnonneg hsup ε hε hReverse z hz hbound.1
        ρ R hρ hρR hR
      have hSigned' : normalizedLpMoment (χ * (pC * v)) (by positivity)
          (originCube ρ) F ^ (pC * v) ≤
        K * normalizedLpMoment (pC * v) (mul_pos hpC hv) (originCube R) F ^ (pC * v) := by
        simpa only [hzabs, hWhich, r, χ, chiParam, γ₅, β, Θ, K, ENNReal.rpow_eq_pow] using hSigned
      have hFρ := ae_restrict_of_ae_restrict_of_subset
        (Scalar.originCube_subset_of_le_one (by linarith : ρ ≤ 1)) hFpos
      have hFR := ae_restrict_of_ae_restrict_of_subset
        (Scalar.originCube_subset_of_le_one hR) hFpos
      have hscaled := normalizedLpMoment_power_step (originCube ρ) (originCube R)
        (Scalar.measurableSet_originCube ρ) (Scalar.measurableSet_originCube R) F
        hχpos hpC hv hFρ hFR K hSigned'
      have hcost := small_reverse_cost_le_exp (γ := γ₅) hC1 hCtop hΘtop
        (sub_pos.mpr hρR) hr hβ hbound.2
      exact hscaled.trans (mul_le_mul_of_nonneg_right hcost zero_le)
    intro b ρ R hb hb1 hρ hρR hR
    exact small_moment_iteration_of_log_step hχ hA (mul_pos hγ hr).le f hfmeas
      hsmall hb hb1 (by linarith) hρR (by linarith)
  constructor
  · intro b ρ R hb hb1 hρ hρR hR
    have h := run false (b := b) (ρ := ρ) (R := R) hb hb1 hρ hρR hR
    simpa only [Bool.false_eq_true, ite_false, pC, A, β, γ₅, r, χ] using h
  · intro b ρ R hb hb1 hρ hρR hR
    have h := run true (b := b) (ρ := ρ) (R := R) hb hb1 hρ hρR hR
    have hfun : (fun x => ((u x + ε)⁻¹) ^ pC) =
        (fun x => (u x + ε) ^ (-pC)) := by
      funext x
      exact (Real.rpow_neg_eq_inv_rpow _ _).symm
    simpa only [ite_true, hfun, pC, A, β, γ₅, r, χ] using h

end CoarseDeGiorgi.Harnack.Iterations
