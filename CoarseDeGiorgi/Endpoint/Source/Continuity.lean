module

public import CoarseDeGiorgi.Endpoint.Source.Functional
public import CoarseDeGiorgi.Weighted.Truncation.Chain
public import CoarseDeGiorgi.Weighted.Truncation.Energy

/-! The continuity bound `∫ |φ| dμ ≤ ℰ(φ)^{1/2} ℰ(∇u)^{1/2}` for a measure representing the flux. -/

@[expose] public section

namespace CoarseDeGiorgi.Endpoint

open Homogenization MeasureTheory Filter Topology

variable {d : ℕ} {V : Set (Vec d)} {a : CoeffField d}

/-- A continuous function vanishing off a compact subset of `V` is integrable
for a measure that is finite on compact subsets of `V`. -/
theorem integrable_of_supported {μ : Measure (Vec d)}
    (hμ : ∀ K : Set (Vec d), IsCompact K → K ⊆ V → μ K < ⊤) {f : Vec d → ℝ}
    {K : Set (Vec d)} (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : Continuous f) (hz : ∀ x, x ∉ K → f x = 0) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support
    (HasCompactSupport.intro hK hz)
  have h1 : IntegrableOn f K μ :=
    Measure.integrableOn_of_bounded (hμ _ hK hKV).ne hf.aestronglyMeasurable
      (ae_of_all _ fun x => hC x)
  exact h1.integrable_of_forall_notMem_eq_zero fun x hx => hz x hx

/-- The smoothed absolute value. -/
noncomputable def softAbs (ε : ℝ) (t : ℝ) : ℝ := Real.sqrt (t ^ 2 + ε ^ 2) - ε

theorem softAbs_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (softAbs ε) := by
  unfold softAbs
  refine ContDiff.sub (ContDiff.sqrt ((contDiff_id.pow 2).add contDiff_const) fun t => ?_)
    contDiff_const
  positivity

theorem softAbs_zero (ε : ℝ) (hε : 0 < ε) : softAbs ε 0 = 0 := by
  simp [softAbs, Real.sqrt_sq hε.le]

theorem softAbs_nonneg {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ softAbs ε t := by
  unfold softAbs
  have : ε ≤ Real.sqrt (t ^ 2 + ε ^ 2) := by
    rw [Real.le_sqrt' hε]
    nlinarith [sq_nonneg t]
  linarith

theorem abs_le_softAbs_add (ε : ℝ) (t : ℝ) : |t| ≤ softAbs ε t + ε := by
  unfold softAbs
  have : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
  linarith

theorem abs_deriv_softAbs_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) : |deriv (softAbs ε) t| ≤ 1 := by
  have hpos : t ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have hd : HasDerivAt (softAbs ε) ((2 * t) / (2 * Real.sqrt (t ^ 2 + ε ^ 2))) t := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + ε ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).add_const (ε ^ 2)
    exact (h1.sqrt hpos).sub_const ε
  rw [hd.deriv]
  have hs : 0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.sqrt (t ^ 2 + ε ^ 2)),
    div_le_one (by positivity)]
  have := Real.abs_le_sqrt (x := t) (y := t ^ 2 + ε ^ 2) (by nlinarith [sq_nonneg ε])
  rw [abs_mul, abs_two]
  linarith

/-- The smoothed absolute value of a test function has no larger energy. -/
theorem energy_softAbs_le (hV : IsOpen V) (ha : IsWeightedCoeffOn V a) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {ε : ℝ} (hε : 0 < ε) :
    weightedEnergy a V (smoothGrad (softAbs ε ∘ φ)) ≤ weightedEnergy a V (smoothGrad φ) := by
  have := Weighted.energy_mul_le ha (G := smoothGrad φ) (b := fun x => deriv (softAbs ε) (φ x))
    (M := 1) (ae_of_all _ fun x => abs_deriv_softAbs_le hε (φ x))
  rw [one_pow, ENNReal.ofReal_one, one_mul] at this
  exact (Weighted.energy_congr_ae
    (Weighted.smoothGrad_comp_ae hV hφ.contDiffOn (softAbs_contDiff hε))).trans_le this

/-- `∫ |φ| dμ ≤ ℰ(φ)^{1/2} ℰ(G)^{1/2}` for a measure representing the flux of `G`. -/
theorem integral_abs_le (hV : IsOpen V) (ha : IsWeightedCoeffOn V a)
    {G : Vec d → Vec d} (hG : AEStronglyMeasurable G (volume.restrict V))
    (hEG : weightedEnergy a V G < ⊤) {μ : Measure (Vec d)}
    (hμ : ∀ K : Set (Vec d), IsCompact K → K ⊆ V → μ K < ⊤)
    (hrep : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V → ∫ x, φ x ∂μ = fluxPairing a V G φ)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ V) :
    ∫ x, |φ x| ∂μ ≤ Real.sqrt (weightedEnergy a V (smoothGrad φ)).toReal *
      Real.sqrt (weightedEnergy a V G).toReal := by
  obtain ⟨χ, hχ, hχc, hχs, hχ01, hχ1⟩ := exists_cutoff01 hV hc hs
  have hχint : Integrable χ μ := integrable_of_supported hμ hχc hχs hχ.continuous
    (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have hEφ : weightedEnergy a V (smoothGrad φ) < ⊤ := (Weighted.isSmoothCore_of_supported ha hφ hc).2.2
  have hint_abs : Integrable (fun x => |φ x|) μ :=
    integrable_of_supported hμ hc hs hφ.continuous.abs
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, abs_zero])
  have hc0 : 0 ≤ ∫ x, χ x ∂μ := integral_nonneg fun x => (hχ01 x).1
  have key : ∀ ε : ℝ, 0 < ε → ∫ x, |φ x| ∂μ ≤
      Real.sqrt (weightedEnergy a V (smoothGrad φ)).toReal *
        Real.sqrt (weightedEnergy a V G).toReal + ε * ∫ x, χ x ∂μ := by
    intro ε hε
    have hsm := softAbs_contDiff hε
    have hφε : ContDiff ℝ (⊤ : ℕ∞) (softAbs ε ∘ φ) := hsm.comp hφ
    have hcε : HasCompactSupport (softAbs ε ∘ φ) := hc.comp_left (softAbs_zero ε hε)
    have hsε : tsupport (softAbs ε ∘ φ) ⊆ V :=
      (tsupport_comp_subset (softAbs_zero ε hε) φ).trans hs
    have hint_ε : Integrable (softAbs ε ∘ φ) μ :=
      integrable_of_supported hμ hc hs (hsm.continuous.comp hφ.continuous)
        (fun x hx => by
          simp only [Function.comp, image_eq_zero_of_notMem_tsupport hx, softAbs_zero ε hε])
    have h1 : ∫ x, (softAbs ε ∘ φ) x ∂μ ≤ Real.sqrt (weightedEnergy a V (smoothGrad φ)).toReal *
        Real.sqrt (weightedEnergy a V G).toReal := by
      rw [hrep _ hφε hcε hsε]
      refine (le_abs_self _).trans ((fluxPairing_bound hV ha hG hEG hφε hcε hsε).trans ?_)
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
        (ENNReal.toReal_mono hEφ.ne (energy_softAbs_le hV ha hφ hε))) (Real.sqrt_nonneg _)
    have h2 : ∫ x, |φ x| ∂μ ≤ ∫ x, ((softAbs ε ∘ φ) x + ε * χ x) ∂μ := by
      refine integral_mono hint_abs (hint_ε.add (hχint.const_mul ε)) fun x => ?_
      by_cases hx : x ∈ tsupport φ
      · rw [hχ1 x hx]
        have := abs_le_softAbs_add ε (φ x)
        simp only [Function.comp, mul_one]
        linarith
      · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
        have := softAbs_nonneg hε (φ x)
        have := (hχ01 x).1
        simp only [Function.comp]
        positivity
    rw [integral_add hint_ε (hχint.const_mul ε), integral_const_mul] at h2
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hc1 : 0 < ∫ x, χ x ∂μ + 1 := by linarith
  have := key (δ / (∫ x, χ x ∂μ + 1)) (by positivity)
  have h3 : δ / (∫ x, χ x ∂μ + 1) * ∫ x, χ x ∂μ ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hc1]
    nlinarith
  linarith

end CoarseDeGiorgi.Endpoint
