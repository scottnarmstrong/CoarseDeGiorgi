import CoarseDeGiorgi.Harnack.Iterations.SignedEndpointIterations
import CoarseDeGiorgi.Harnack.Iterations.NormalizedSmallSignedIterations

open Homogenization MeasureTheory
open scoped ENNReal
namespace CoarseDeGiorgi.Harnack.Iterations

/-- All three source iterations and the crossover all-radii estimates with one
common parameter constant, for every admissible crossover constant `c`.
-/
theorem uniform_three_iterations_of_power_caccioppoli
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
    ∃ C₃ γ₆ : ℝ, 1 ≤ C₃ ∧ 0 < γ₆ ∧
    ∀ (c : ℝ) (hc : 0 < c)
      (hcRange : c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)))
      (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
      (hrange : spatialMomentRange a ha p q s t)
      (u : Vec d → ℝ) (G : Vec d → Vec d)
      (_hsup : IsWeightedSupersolution a (originCube 1) u G)
      (_hnonneg : ∀ᵐ x ∂volume.restrict (originCube 1), 0 ≤ u x)
      (ε : ℝ) (_hε : 0 < ε),
    let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
    ((∀ {e b ρ R : ℝ} (he : 0 < e) (heb : e < b), b ≤ 1 → 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
      normalizedLpMoment b (he.trans heb) (originCube ρ) (fun x => (u x + ε) ^ pC) ≤
        (ENNReal.ofReal (C₃ * (R - ρ) ^ (-γ₆))) ^ (1 / e) *
          normalizedLpMoment e he (originCube R) (fun x => (u x + ε) ^ pC)) ∧
    (∀ {e b ρ R : ℝ} (he : 0 < e) (heb : e < b), b ≤ 1 → 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
      normalizedLpMoment b (he.trans heb) (originCube ρ) (fun x => (u x + ε) ^ (-pC)) ≤
        (ENNReal.ofReal (C₃ * (R - ρ) ^ (-γ₆))) ^ (1 / e) *
          normalizedLpMoment e he (originCube R) (fun x => (u x + ε) ^ (-pC)))) ∧
    (∀ {ρ R : ℝ}, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
    let H := (ENNReal.ofReal (C₃ *
      (R - ρ) ^ (-γ₆))) ^ (1 / pC)
    (normalizedLpMoment pC
      (iteration_crossoverExponent_pos hd hp hq hs ht hθ c hc hcRange a ha hrange)
      (originCube R) (fun x => (u x + ε)⁻¹))⁻¹ ≤
      H * nonnegativeEssInf (originCube ρ) (fun x => u x + ε) ∧
    normalizedLpMoment (paramR q / 4) (by
      have h := ReverseMoments.paramR_pos_of_harnack_facts hd hp hq hs ht hθ
      positivity) (originCube ρ) (fun x => u x + ε) ≤
      H * normalizedLpMoment pC
        (iteration_crossoverExponent_pos hd hp hq hs ht hθ c hc hcRange a ha hrange)
        (originCube R) (fun x => u x + ε)) ∧
    ((∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (fun x => (u x + ε) ^ pC) 1 (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
          eLpNorm (fun x => (u x + ε) ^ pC) (ENNReal.ofReal b)
            (volume.restrict (originCube R))) ∧
    (∀ {b ρ R : ℝ}, 0 < b → b < 1 → 3 / 4 ≤ ρ → ρ < R → R ≤ 7 / 8 →
      eLpNorm (fun x => (u x + ε) ^ (-pC)) 1 (volume.restrict (originCube ρ)) ≤
        (ENNReal.ofReal (((2 : ℝ) ^ d * C₃) * (R - ρ) ^ (-γ₆))) ^ (1 / b) *
          eLpNorm (fun x => (u x + ε) ^ (-pC)) (ENNReal.ofReal b)
            (volume.restrict (originCube R))))
 := by
  obtain ⟨C, hC1, hCtop, hReverse⟩ :=
    ReverseMoments.signed_power_normalized_reverse_of_power_caccioppoli
      hPowerCaccioppoli hd hp hq hs ht hθ
  let r := paramR q
  let χ := chiParam d q t
  let γ₅ := gammaOneParam (d := d) q t +
    gammaTwoParam (d := d) p q t * alphaParam t / paramTheta d p q s t
  let β := alphaParam t * r / (2 * paramTheta d p q s t)
  let A := Real.log C.toReal + (γ₅ * r + β) * Real.log 2
  let B := A * (χ / (χ - 1)) +
    (γ₅ * r * Real.log 2 + 2 * β * Real.log χ) * (χ ^ 2 / (χ - 1) ^ 2)
  let C₃ := (2 : ℝ) ^ d * Real.exp B
  let γ₆ := γ₅ * r * χ / (χ - 1)
  obtain ⟨hα, _, hr1, _, _, _, _, hrStar⟩ :=
    Assembly.Hybrid.embedding_parameter_facts hd hp hq hs ht hθ
  have hr : 0 < r := zero_lt_one.trans hr1
  have hχ : 1 < χ := by
    dsimp [χ, chiParam]
    exact (lt_div_iff₀ hr).2 (by simpa using hrStar)
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
  have hC₃ : 1 ≤ C₃ := by
    have hB : 0 ≤ B := by
      dsimp [B]
      have hlog2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      have hlogχ := Real.log_nonneg hχ.le
      have hχpos := zero_lt_one.trans hχ
      have hχsub := sub_pos.mpr hχ
      positivity
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (Real.one_le_exp_iff.mpr hB)
  have hγ₆ : 0 < γ₆ := by
    dsimp [γ₆]
    have hχpos := zero_lt_one.trans hχ
    have hχsub := sub_pos.mpr hχ
    positivity
  let Bsmall := A * (χ / (χ - 1)) + γ₅ * r * Real.log 2 * (χ ^ 2 / (χ - 1) ^ 2)
  have hBsmall : Bsmall ≤ B := by
    have hlogχ := Real.log_nonneg hχ.le
    have hχpos := zero_lt_one.trans hχ
    have hχsub := sub_pos.mpr hχ
    have hextra : 0 ≤ 2 * β * Real.log χ * (χ ^ 2 / (χ - 1) ^ 2) := by positivity
    dsimp [Bsmall, B]
    nlinarith
  have hD : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hCnorm : (2 : ℝ) ^ d * Real.exp Bsmall ≤ C₃ :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hBsmall) (by positivity)
  have hCraw : Real.exp Bsmall ≤ C₃ :=
    (le_mul_of_one_le_left (Real.exp_pos _).le hD).trans hCnorm
  refine ⟨C₃, γ₆, hC₃, hγ₆, ?_⟩
  intro c hc hcRange a ha hrange u G hsup hnonneg ε hε
  have hrinput := hReverse a ha hrange u G hnonneg hsup ε hε
  have hnorm := normalized_small_signed_iterations_of_normalized_reverse hd hp hq hs ht hθ
    C hC1 hCtop c hc hcRange a ha hrange u G hsup hnonneg ε hε hrinput
  have hraw := small_signed_iterations_of_normalized_reverse hd hp hq hs ht hθ
    C hC1 hCtop c hc hcRange a ha hrange u G hsup hnonneg ε hε hrinput
  have hfactor {K L δ z : ℝ} (hKL : K ≤ L) (hz : 0 < z) (hδ : 0 < δ) :
      ENNReal.ofReal (K * δ ^ (-γ₆)) ^ (1 / z) ≤
        ENNReal.ofReal (L * δ ^ (-γ₆)) ^ (1 / z) :=
    ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hKL (Real.rpow_nonneg hδ.le _))) (by positivity)
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩⟩
  · intro e b ρ R he heb hb1 hρ hρR hR
    exact (hnorm.1 he heb hb1 hρ hρR hR).trans
      (mul_le_mul_of_nonneg_right (hfactor hCnorm he (sub_pos.mpr hρR)) zero_le)
  · intro e b ρ R he heb hb1 hρ hρR hR
    exact (hnorm.2 he heb hb1 hρ hρR hR).trans
      (mul_le_mul_of_nonneg_right (hfactor hCnorm he (sub_pos.mpr hρR)) zero_le)
  · intro ρ R hρ hρR hR
    have h := signed_endpoint_iterations_of_normalized_reverse hd hp hq hs ht hθ
      C hC1 hCtop c hc hcRange a ha hrange u G hsup hnonneg ε hε hrinput hρ hρR hR
    let pc := crossoverExponent c a ha s t p q hs ht hp.le hq.le
    let H := ENNReal.ofReal (C₃ * (R - ρ) ^ (-γ₆)) ^ (1 / pc)
    have hpc : 0 < pc := iteration_crossoverExponent_pos hd hp hq hs ht hθ c hc hcRange a ha hrange
    have hbase : 0 < ENNReal.ofReal (C₃ * (R - ρ) ^ (-γ₆)) :=
      ENNReal.ofReal_pos.mpr (mul_pos (zero_lt_one.trans_le hC₃)
        (Real.rpow_pos_of_pos (sub_pos.mpr hρR) _))
    have hHpos : 0 < H := ENNReal.rpow_pos hbase ENNReal.ofReal_ne_top
    have hHtop : H ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    exact ⟨reciprocal_iteration_bound_rearrange hHpos hHtop h.1, h.2⟩
  · intro b ρ R hb hb1 hρ hρR hR
    exact (hraw.1 hb hb1 hρ hρR hR).trans
      (mul_le_mul_of_nonneg_right
        (hfactor (mul_le_mul_of_nonneg_left hCraw (by positivity)) hb (sub_pos.mpr hρR)) zero_le)
  · intro b ρ R hb hb1 hρ hρR hR
    exact (hraw.2 hb hb1 hρ hρR hR).trans
      (mul_le_mul_of_nonneg_right
        (hfactor (mul_le_mul_of_nonneg_left hCraw (by positivity)) hb (sub_pos.mpr hρR)) zero_le)

end CoarseDeGiorgi.Harnack.Iterations
