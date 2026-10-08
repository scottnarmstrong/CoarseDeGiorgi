module

public import CoarseDeGiorgi.Statements.Contrast
public import CoarseDeGiorgi.Statements.ParamTheta
public import CoarseDeGiorgi.Statements.PositivePart
public import CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import CoarseDeGiorgi.Statements.IsWeightedSolution
public import CoarseDeGiorgi.SharpnessExamples.OptimalPowersConstruction
public import CoarseDeGiorgi.SharpnessExamples.PolynomialEllipticity
public import CoarseDeGiorgi.SharpnessExamples.PolynomialTraces
public import CoarseDeGiorgi.SharpnessExamples.PolynomialNormExports
public import CoarseDeGiorgi.SharpnessExamples.OptimalPowersMoments
public import CoarseDeGiorgi.SharpnessExamples.OptimalPowersLower
public import CoarseDeGiorgi.SharpnessExamples.OptimalPowersCombine
public import CoarseDeGiorgi.SharpnessExamples.OptimalPowersFailure

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

theorem optimal_powers_proved (d : ℕ) (_hd : 3 ≤ d) (p q s t : ℝ)
    (hp : 1 < p) (hq : 1 < q) (hs : 0 < s) (ht : 0 < t)
    (_hθ : 0 < paramTheta d p q s t) :
    ∃ (a : ℝ → CoeffField d) (u : ℝ → Vec d → ℝ) (G : ℝ → Vec d → Vec d)
      (ha : ∀ ε, IsWeightedCoeffOn (originCube 1) (a ε)),
      -- each field is symmetric and uniformly elliptic, with constants depending on ε
      (∀ ε, 0 < ε → ε < 1 / 8 → ∃ lam Λ : ℝ, 0 < lam ∧
        ∀ᵐ x ∂(volume.restrict (originCube 1)), (a ε x).IsHermitian ∧
          ∀ ξ : Vec d, lam * vecDot ξ ξ ≤ vecDot ξ (matVecMul (a ε x) ξ) ∧
            vecDot ξ (matVecMul (a ε x) ξ) ≤ Λ * vecDot ξ ξ) ∧
      -- u_ε is a weighted solution for a_ε, and its positive part a weighted subsolution
      (∀ ε, 0 < ε → ε < 1 / 8 → IsWeightedSolution (a ε) (originCube 1) (u ε) (G ε) ∧
        ∃ G' : Vec d → Vec d,
          IsWeightedSubsolution (a ε) (originCube 1) (positivePart (u ε)) G') ∧
      -- uniformly integrable traces
      (∃ C : ℝ, ∀ ε, 0 < ε → ε < 1 / 8 →
        ∫ x in originCube 1, ((a ε x).trace + ((a ε x)⁻¹).trace) ≤ C) ∧
      -- the moments: Λ_ε ≍ ε^{-2θ}, λ_ε ≍ 1, Θ_ε ≍ ε^{-2θ}
      (∃ C : ℝ, 1 ≤ C ∧ ∀ ε, 0 < ε → ε < 1 / 8 →
        ENNReal.ofReal (C⁻¹ * ε ^ (-(2 * paramTheta d p q s t))) ≤
            upperMoment (a ε) (ha ε) s p hs hp.le ∧
          upperMoment (a ε) (ha ε) s p hs hp.le ≤
            ENNReal.ofReal (C * ε ^ (-(2 * paramTheta d p q s t))) ∧
          ENNReal.ofReal C⁻¹ ≤ lowerMoment (a ε) (ha ε) t q ht hq.le ∧
          lowerMoment (a ε) (ha ε) t q ht hq.le ≤ ENNReal.ofReal C ∧
          ENNReal.ofReal (C⁻¹ * ε ^ (-(2 * paramTheta d p q s t))) ≤
            contrast (a ε) (ha ε) s t p q hs ht hp.le hq.le ∧
          contrast (a ε) (ha ε) s t p q hs ht hp.le hq.le ≤
            ENNReal.ofReal (C * ε ^ (-(2 * paramTheta d p q s t)))) ∧
      -- the height of the positive part
      (∀ ε, 0 < ε → ε < 1 / 8 → ∀ ρ : ℝ, 1 / 2 ≤ ρ → ρ < 1 →
        eLpNorm (positivePart (u ε)) ⊤ (volume.restrict (originCube ρ)) =
          ENNReal.ofReal (1 + ρ ^ 2 / 4)) ∧
      -- the L^η norm of the positive part: ≍ ε^{(d-1)/η}, uniformly in ε and R
      (∀ η : ℝ, 0 < η → ∃ C : ℝ, 1 ≤ C ∧ ∀ ε, 0 < ε → ε < 1 / 8 → ∀ R : ℝ, 1 / 2 < R → R ≤ 1 →
        ENNReal.ofReal (C⁻¹ * ε ^ (((d : ℝ) - 1) / η)) ≤
            eLpNorm (positivePart (u ε)) (ENNReal.ofReal η) (volume.restrict (originCube R)) ∧
          eLpNorm (positivePart (u ε)) (ENNReal.ofReal η) (volume.restrict (originCube R)) ≤
            ENNReal.ofReal (C * ε ^ (((d : ℝ) - 1) / η))) ∧
      -- consequently the ratio tends to ∞: the powers of Θ in Theorem A and Corollary B cannot be lowered
      (∀ ρ R η υ : ℝ, 1 / 2 ≤ ρ → ρ < R → R ≤ 1 → 0 < η → η ≤ 2 →
        υ < ((d : ℝ) - 1) / (2 * η * paramTheta d p q s t) →
        Tendsto (fun ε => eLpNorm (positivePart (u ε)) ⊤ (volume.restrict (originCube ρ)) /
            ((contrast (a ε) (ha ε) s t p q hs ht hp.le hq.le).rpow υ *
              eLpNorm (positivePart (u ε)) (ENNReal.ofReal η) (volume.restrict (originCube R))))
          (𝓝[>] 0) (𝓝 ⊤)) := by
  have : NeZero d := ⟨by omega⟩
  let u0 : ℝ → Vec d → ℝ := fun epsilon =>
    CoarseDeGiorgi.SharpnessExamples.polynomialSolution d q t epsilon
  let G0 : ℝ → Vec d → Vec d := fun epsilon =>
    CoarseDeGiorgi.SharpnessExamples.polynomialGradient d q t epsilon
  have h_elliptic : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ∃ lam Λ : ℝ, 0 < lam ∧
        ∀ᵐ x ∂(volume.restrict (originCube 1)),
          (CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily d q t epsilon x).IsHermitian ∧
          ∀ ξ : Vec d,
            lam * vecDot ξ ξ ≤ vecDot ξ
              (matVecMul (CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily d q t epsilon x) ξ) ∧
            vecDot ξ (matVecMul
              (CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily d q t epsilon x) ξ) ≤
              Λ * vecDot ξ ξ := by
    intro epsilon he he8
    exact CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily_ellipticity (d := d) _hd
      (p := p) (q := q) (s := s) (t := t) (epsilon := epsilon)
      hp hq hs ht _hθ he he8
  have h_solution : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      IsWeightedSolution
          (CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily d q t epsilon) (originCube 1)
          (u0 epsilon) (G0 epsilon) ∧
        ∃ G' : Vec d → Vec d,
          IsWeightedSubsolution
            (CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily d q t epsilon) (originCube 1)
            (positivePart (u0 epsilon)) G' := by
    intro epsilon he he8
    simpa only [u0, G0] using
      CoarseDeGiorgi.SharpnessExamples.optimalPowers_solution_posPartSubsolution
        (d := d) _hd (q := q) (t := t) he he8
  have h_traces := CoarseDeGiorgi.SharpnessExamples.polynomialCoefficientFamily_trace_integral_bound (d := d) _hd
    (p := p) (q := q) (s := s) (t := t) hp hq hs ht _hθ
  have h_height : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ∀ rho : ℝ, 1 / 2 ≤ rho → rho < 1 →
        eLpNorm (positivePart (u0 epsilon)) ⊤ (volume.restrict (originCube rho)) =
          ENNReal.ofReal (1 + rho ^ 2 / 4) := by
    intro epsilon he he8 rho hrho hrho1
    exact CoarseDeGiorgi.SharpnessExamples.polynomialPositivePart_height_of_solution
      (d := d) _hd h_solution (epsilon := epsilon) (rho := rho)
      he he8 hrho hrho1
  have h_lp := fun eta heta =>
    CoarseDeGiorgi.SharpnessExamples.polynomialPositivePart_Lp_asymptotic_of_solution (d := d) _hd
      (q := q) (t := t) (eta := eta) heta h_solution
  -- the upper bounds from coefficient averages, and the lower bound from Theorem A
  obtain ⟨Cu, hCu1, hup⟩ := optimalPowers_upper_bounds _hd hp hq hs ht _hθ
  obtain ⟨K, hK, hA⟩ := optimalPowers_theoremA_inequality d _hd p q s t hp hq hs ht _hθ
  obtain ⟨B2, hB21, hB2⟩ := h_lp 2 (by norm_num)
  have hdR : 0 < (d : ℝ) - 1 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast _hd
    linarith
  have hB20 : 0 < B2 := lt_of_lt_of_le zero_lt_one hB21
  have he0 : 0 < ((d : ℝ) - 1) / (4 * paramTheta d p q s t) := by positivity
  set e : ℝ := ((d : ℝ) - 1) / (4 * paramTheta d p q s t) with he_def
  set c : ℝ := ((K * B2)⁻¹) ^ (1 / e) with hc_def
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hcontrast : ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ENNReal.ofReal (c * epsilon ^ (-(2 * paramTheta d p q s t))) ≤
        contrast (polynomialCoefficientFamily d q t epsilon)
          (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) s t p q hs ht hp.le hq.le := by
    intro epsilon he he8
    obtain ⟨hUp, hLo⟩ := hup epsilon he he8
    have hC0 : 0 < Cu := lt_of_lt_of_le zero_lt_one hCu1
    have hU : upperMoment (polynomialCoefficientFamily d q t epsilon)
        (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) s p hs hp.le < ⊤ :=
      hUp.trans_lt ENNReal.ofReal_lt_top
    have hL : 0 < lowerMoment (polynomialCoefficientFamily d q t epsilon)
        (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) t q ht hq.le :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.2 (inv_pos.2 hC0)) hLo
    have hTtop : contrast (polynomialCoefficientFamily d q t epsilon)
        (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) s t p q hs ht hp.le hq.le ≠ ⊤ := by
      have h1 := ENNReal.div_le_div hUp hLo
      rw [← ENNReal.ofReal_div_of_pos (inv_pos.2 hC0)] at h1
      exact (h1.trans_lt ENNReal.ofReal_lt_top).ne
    obtain ⟨G', hG'⟩ := (h_solution epsilon he he8).2
    have hhi : 1 ≤ eLpNorm (positivePart (u0 epsilon)) ⊤
        (volume.restrict (originCube (1 / 2))) := by
      rw [h_height epsilon he he8 (1 / 2) le_rfl (by norm_num)]
      exact ENNReal.one_le_ofReal.2 (by norm_num)
    have hineq := hA _ (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) (u0 epsilon) G'
      hU hL hG' hhi
    have hL2 := (hB2 epsilon he he8 (3 / 4) (by norm_num) (by norm_num)).2
    have hy : 0 < epsilon ^ (((d : ℝ) - 1) / 2) := Real.rpow_pos_of_pos he _
    have hsolve := optimalPowers_solve_for_contrast hTtop hK hB20 hy he0
      (hineq.trans (mul_le_mul' le_rfl hL2))
    refine le_trans (le_of_eq ?_) hsolve
    congr 1
    have hθ0 := _hθ
    rw [show ((K * B2) * epsilon ^ (((d : ℝ) - 1) / 2))⁻¹ =
        (K * B2)⁻¹ * (epsilon ^ (((d : ℝ) - 1) / 2))⁻¹ from mul_inv _ _,
      Real.mul_rpow (by positivity) (by positivity), hc_def, ← Real.rpow_neg he.le,
      ← Real.rpow_mul he.le]
    congr 2
    rw [he_def]
    field_simp
    norm_num
  have hall := fun (epsilon : ℝ) (he : 0 < epsilon) (he8 : epsilon < 1 / 8) =>
    optimalPowers_combine (L := upperMoment (polynomialCoefficientFamily d q t epsilon)
        (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) s p hs hp.le)
      (l := lowerMoment (polynomialCoefficientFamily d q t epsilon)
        (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) t q ht hq.le)
      (Real.rpow_pos_of_pos he (-(2 * paramTheta d p q s t))) hCu1 hc0 rfl
      (hup epsilon he he8).1 (hup epsilon he he8).2 (hcontrast epsilon he he8)
  refine ⟨polynomialCoefficientFamily d q t, u0, G0,
    optimalPowers_family_weightedCoeffOn d _hd q t,
    h_elliptic, h_solution, h_traces, ?_, h_height, h_lp, ?_⟩
  · refine ⟨optimalPowersConst Cu c, optimalPowersConst_one_le Cu c, ?_⟩
    intro epsilon he he8
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hall epsilon he he8
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · intro ρ R η υ hρ hρR hR hη hη2 hυ
    obtain ⟨B, hB1, hBlp⟩ := h_lp η hη
    have hρ1 : ρ < 1 := hρR.trans_le hR
    have hRhalf : 1 / 2 < R := hρ.trans_lt hρR
    have hθ2 : 0 < 2 * paramTheta d p q s t := by positivity
    have hb : 0 < ((d : ℝ) - 1) / η := div_pos hdR hη
    have hthreshold : υ < (((d : ℝ) - 1) / η) / (2 * paramTheta d p q s t) := by
      convert hυ using 1; field_simp
    have hH : 0 < 1 + ρ ^ 2 / 4 := by positivity
    have hgen := optimalPowers_ratio_tendsto_top
      (fun epsilon => contrast (polynomialCoefficientFamily d q t epsilon)
        (optimalPowers_family_weightedCoeffOn d _hd q t epsilon) s t p q hs ht hp.le hq.le)
      (fun epsilon => eLpNorm (positivePart (u0 epsilon)) (ENNReal.ofReal η)
        (volume.restrict (originCube R)))
      hθ2 (optimalPowersConst_one_le Cu c) hB1 hH hthreshold
      (fun epsilon he he8 => (hall epsilon he he8).2.2.2.2.2)
      (fun epsilon he he8 => (hall epsilon he he8).2.2.2.2.1)
      (fun epsilon he he8 => (hBlp epsilon he he8 R hRhalf hR).2)
    apply hgen.congr'
    have he8 : ∀ᶠ epsilon : ℝ in 𝓝[>] 0, epsilon < 1 / 8 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
    filter_upwards [self_mem_nhdsWithin, he8] with epsilon he he8
    rw [h_height epsilon he he8 ρ hρ hρ1]
    rfl

end CoarseDeGiorgi.SharpnessExamples
