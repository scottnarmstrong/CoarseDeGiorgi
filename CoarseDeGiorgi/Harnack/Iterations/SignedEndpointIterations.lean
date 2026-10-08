import CoarseDeGiorgi.Harnack.Iterations.SmallSignedIterations
import CoarseDeGiorgi.Harnack.Iterations.EndpointIterations
import CoarseDeGiorgi.Harnack.Iterations.GeometricPowerFactor
import CoarseDeGiorgi.Harnack.Iterations.GeometricReverseCost

open Homogenization MeasureTheory
open scoped ENNReal
namespace CoarseDeGiorgi.Harnack.Iterations

theorem iteration_crossoverExponent_pos {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (hθ : 0 < paramTheta d p q s t) (c : ℝ) (hc : 0 < c)
    (hcRange : c ≤ min (1 / 2) (paramR q / (16 * chiParam d q t)))
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t) :
    0 < crossoverExponent c a ha s t p q hs ht hp.le hq.le := by
  rcases hrange with ⟨_, _, _, _, _, _, _, _, _, hUpper, hLower⟩
  exact (ruled_exponent_range_of_moment_comparison hd p q s t hp hq hs ht hθ a ha
    ⟨Moments.moment_contrast_ge_one (by omega) a ha hs ht hp.le hq.le hUpper hLower,
      ENNReal.div_lt_top hUpper.ne hLower.ne'⟩ c hc
    (by simpa [chiParam] using hcRange)).1

/-- The source endpoint estimates for every admissible crossover constant `c`, from the
normalized reverse estimate.
-/
theorem signed_endpoint_iterations_of_normalized_reverse {d : ℕ}
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
    let B := A * (χ / (χ - 1)) +
      (γ₅ * r * Real.log 2 + 2 * β * Real.log χ) * (χ ^ 2 / (χ - 1) ^ 2)
    let γ₆ := γ₅ * r * χ / (χ - 1)
    let pC := crossoverExponent c a ha s t p q hs ht hp.le hq.le
    ∀ {ρ R : ℝ}, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 →
    let H := (ENNReal.ofReal (((2 : ℝ) ^ d * Real.exp B) *
      (R - ρ) ^ (-γ₆))) ^ (1 / pC)
    (H * normalizedLpMoment pC
      (iteration_crossoverExponent_pos hd hp hq hs ht hθ c hc hcRange a ha hrange)
      (originCube R) (fun x => (u x + ε)⁻¹))⁻¹ ≤
      nonnegativeEssInf (originCube ρ) (fun x => u x + ε) ∧
    normalizedLpMoment (r / 4) (by
      have h := ReverseMoments.paramR_pos_of_harnack_facts hd hp hq hs ht hθ
      positivity) (originCube ρ) (fun x => u x + ε) ≤
      H * normalizedLpMoment pC
        (iteration_crossoverExponent_pos hd hp hq hs ht hθ c hc hcRange a ha hrange)
        (originCube R) (fun x => u x + ε)
 := by
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
  have run (negative : Bool) (j : ℕ)
      (hstop : negative = false → pC * χ ^ j < r / 4)
      (ρ R : ℝ) (hρ : 1 / 2 ≤ ρ) (hρR : ρ < R) (hR : R ≤ 1) :
      let F : Vec d → ℝ := fun x => if negative then (u x + ε)⁻¹ else u x + ε
      normalizedLpMoment (pC * χ ^ (j + 1)) (by positivity) (originCube ρ) F ^ (pC * χ ^ j) ≤
        ENNReal.ofReal (Real.exp (A + γ₅ * r * Real.log (1 / (R - ρ)) +
          2 * β * (j : ℝ) * Real.log χ)) *
          normalizedLpMoment (pC * χ ^ j) (by positivity) (originCube R) F ^ (pC * χ ^ j) := by
    dsimp only
    let z := if negative then -(pC * χ ^ j) else pC * χ ^ j
    let F : Vec d → ℝ := fun x => if negative then (u x + ε)⁻¹ else u x + ε
    have hzshape : (z = pC * χ ^ j ∧ z < r / 4) ∨ z = -(pC * χ ^ j) := by
      cases negative
      · exact Or.inl ⟨rfl, hstop rfl⟩
      · exact Or.inr rfl
    have hbound := geometric_signed_powerFactor_bound j hpC hc.le hr
      Θ.toReal_nonneg hχpos hpCΘ hcsmall hzshape
    have hzabs : |z| = pC * χ ^ j := by
      cases negative <;> simp [z, abs_of_pos (mul_pos hpC (pow_pos hχpos j))]
    have hz : z ≠ 0 := by
      intro heq
      have h := congrArg abs heq
      rw [hzabs, abs_zero] at h
      exact (mul_pos hpC (pow_pos hχpos j)).ne' h
    have hWhich : (fun x => if 0 < z then u x + ε else (u x + ε)⁻¹) = F := by
      cases negative <;> simp [z, F, mul_pos hpC (pow_pos hχpos j),
        not_lt_of_ge (mul_pos hpC (pow_pos hχpos j)).le]
    have hSigned := signed_moment_step_of_normalized_reverse hd hp hq hs ht hθ
      C hC1 hCtop a ha hrange u G hnonneg hsup ε hε hReverse z hz hbound.1
      ρ R hρ hρR hR
    have hcost := geometric_reverse_cost_le_exp (γ := γ₅) j hχ hC1 hCtop hΘtop
      (sub_pos.mpr hρR) hr hβ hbound.2
    have hexnext : χ * (pC * χ ^ j) = pC * χ ^ (j + 1) := by rw [pow_succ]; ring
    have hexnext' : (rStarParam (d := d) q t / paramR q) *
        (pC * (rStarParam (d := d) q t / paramR q) ^ j) =
        pC * (rStarParam (d := d) q t / paramR q) ^ (j + 1) := by rw [pow_succ]; ring
    have hSigned' : normalizedLpMoment (pC * χ ^ (j + 1)) (by positivity)
        (originCube ρ) F ^ (pC * χ ^ j) ≤
      (C * ENNReal.ofReal (((R - ρ) / 2) ^ (-γ₅)) ^ r *
        (1 + ENNReal.ofReal (powerFactor (z / r) ^ 2) * Θ) ^ β) *
          normalizedLpMoment (pC * χ ^ j) (by positivity) (originCube R) F ^ (pC * χ ^ j) := by
      simpa only [hzabs, hWhich, r, χ, chiParam, γ₅, β, Θ,
        ENNReal.rpow_eq_pow, hexnext'] using hSigned
    exact hSigned'.trans (mul_le_mul_of_nonneg_right hcost zero_le)
  intro ρ R hρ hρR hR
  apply endpoint_iterations_of_geometric_steps hχ hA (mul_pos hγ hr).le hβ
    hpC (by positivity : 0 < r / 4) hpCquarter (fun x => u x + ε) hUmeas hUpos
  · intro j ρ R hρ hρR hR
    simpa only [ite_true] using run true j (by simp) ρ R hρ hρR hR
  · intro j hj ρ R hρ hρR hR
    simpa only [Bool.false_eq_true, ite_false] using run false j (fun _ => hj) ρ R hρ hρR hR

end CoarseDeGiorgi.Harnack.Iterations
