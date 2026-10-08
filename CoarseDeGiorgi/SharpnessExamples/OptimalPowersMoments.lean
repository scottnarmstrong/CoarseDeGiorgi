import CoarseDeGiorgi.SharpnessExamples.OptimalPowersUpper

/-! # The upper bounds `Λ_ε ≤ C ε^{-2θ}` and `λ_ε^{-1} ≤ C` for the polynomial field -/

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.SharpnessExamples

noncomputable section

private theorem op_sqrt_rpow {e : ℝ} (he : 0 ≤ e) (x : ℝ) :
    Real.sqrt (Real.rpow e x) = Real.rpow e (x / 2) := by
  rw [Real.sqrt_eq_rpow]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul he]
  congr 1
  ring

/-- The two coefficient-average bounds for the polynomial field. -/
theorem optimalPowers_upper_bounds {d : ℕ} (hd : 3 ≤ d)
    {p q s t : ℝ} (hp : 1 < p) (hq : 1 < q) (hs : 0 < s)
    (ht : 0 < t) (hθ : 0 < paramTheta d p q s t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      upperMoment (polynomialCoefficientFamily d q t epsilon)
          (optimalPowers_family_weightedCoeffOn d hd q t epsilon) s p hs hp.le ≤
        ENNReal.ofReal (C * epsilon ^ (-(2 * paramTheta d p q s t))) ∧
      ENNReal.ofReal C⁻¹ ≤
        lowerMoment (polynomialCoefficientFamily d q t epsilon)
          (optimalPowers_family_weightedCoeffOn d hd q t epsilon) t q ht hq.le := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn2 : 2 ≤ n := by omega
  have hnR : (((n + 1 : ℕ) : ℝ) - 1) = n := by push_cast; ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hhat : polynomialHatT (n + 1) q t = t + (n : ℝ) / (2 * q) := by
    unfold polynomialHatT; rw [hnR]
  have hθeq : paramTheta (n + 1) p q s t =
      1 - (s + (n : ℝ) / (2 * p)) - polynomialHatT (n + 1) q t := by
    unfold paramTheta polynomialHatT; rw [hnR]; ring
  have hh := optimalPowers_hatT_mem_Ioo hd hp hq hs ht hθ
  have hsp : 0 < s + (n : ℝ) / (2 * p) := by positivity
  have hν1 : 2 * s + (n : ℝ) / p < n := by
    have : 2 * s + (n : ℝ) / p = 2 * (s + (n : ℝ) / (2 * p)) := by field_simp
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    rw [this]; rw [hθeq] at hθ; linarith [hh.1]
  have hν2 : 2 * t + (n : ℝ) / q < n := by
    have : 2 * t + (n : ℝ) / q = 2 * polynomialHatT (n + 1) q t := by
      rw [hhat]; field_simp
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    rw [this]; linarith [hh.2]
  set K1 := cylinderRootConstant n p s (2 * s + (n : ℝ) / p) with hK1
  set K2 := cylinderRootConstant n q t (2 * t + (n : ℝ) / q) with hK2
  have hK1n := optimalPowers_rootConstant_nonneg n (v := p) hs hν1
  have hK2n := optimalPowers_rootConstant_nonneg n (v := q) ht hν2
  have hσs : 0 ≤ 1 - Real.rpow 3 (-s) :=
    sub_nonneg.2 (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)).le
  have hσt : 0 ≤ 1 - Real.rpow 3 (-t) :=
    sub_nonneg.2 (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)).le
  set B1 : ℝ := (1 - Real.rpow 3 (-s)) * (K1 * (Real.sqrt n *
    Real.rpow 2 ((2 * s + (n : ℝ) / p) / 2))) with hB1
  set B2 : ℝ := (1 - Real.rpow 3 (-t)) * (K2 * Real.rpow 2 (polynomialHatT (n + 1) q t)) with hB2
  have hB1n : 0 ≤ B1 := by
    rw [hB1]; have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) ((2 * s + (n : ℝ) / p) / 2)
    positivity
  have hB2n : 0 ≤ B2 := by
    rw [hB2]; have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (polynomialHatT (n + 1) q t)
    positivity
  refine ⟨max 1 (max ((1 + B1) ^ 2) ((1 + B2) ^ 2)), le_max_left _ _, ?_⟩
  intro epsilon he he8
  obtain ⟨hpar, hper, hper1⟩ := optimalPowers_conductivities_bounds hd hp hq hs ht hθ he he8
  have hfield := optimalPowers_family_eq_cylinder (d := n + 1) (q := q) (t := t) he he8
  have hz1 : 1 ≤ Real.rpow epsilon (-paramTheta (n + 1) p q s t) := by
    simpa only [Real.rpow_eq_pow] using Real.one_le_rpow_of_pos_of_le_one_of_nonpos he
      (by linarith) (by linarith)
  have hz2 : Real.rpow epsilon (-paramTheta (n + 1) p q s t) ^ 2 =
      epsilon ^ (-(2 * paramTheta (n + 1) p q s t)) := by
    show (epsilon ^ (-paramTheta (n + 1) p q s t)) ^ 2 = _
    rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
    congr 1; push_cast; ring
  -- both estimates for the cylinder field
  have hup := fun ha => optimalPowers_upperMoment_cylinder_le (n := n) (epsilon := epsilon)
    (A := polynomialParallel (n + 1) q t epsilon)
    (b := polynomialPerpendicular (n + 1) q t epsilon) (s := s) (p := p) he he8 hpar hper hper1
    hs hp.le hν1 ha
  have hlo := fun ha => optimalPowers_lowerMoment_inv_cylinder_le (n := n) (by omega)
    (epsilon := epsilon) (A := polynomialParallel (n + 1) q t epsilon)
    (b := polynomialPerpendicular (n + 1) q t epsilon) (t := t) (q := q) he he8 hpar hper hper1
    ht hq.le hν2 ha
  have key : ∀ (a : CoeffField (n + 1)) (ha : IsWeightedCoeffOn (originCube 1) a),
      a = cylinderCoefficient epsilon (polynomialParallel (n + 1) q t epsilon)
        (polynomialPerpendicular (n + 1) q t epsilon) →
      upperMoment a ha s p hs hp.le ≤ ENNReal.ofReal ((1 + B1 *
        Real.rpow epsilon (-paramTheta (n + 1) p q s t)) ^ 2) ∧
      (lowerMoment a ha t q ht hq.le)⁻¹ ≤ ENNReal.ofReal ((1 + B2) ^ 2) := by
    intro a ha h
    subst h
    have hy1 : (2 * s + (n : ℝ) / p) / 2 = s + (n : ℝ) / (2 * p) := by field_simp
    have hy2 : (2 * t + (n : ℝ) / q) / 2 = polynomialHatT (n + 1) q t := by
      rw [hhat]; field_simp
    have e1 : Real.sqrt (polynomialParallel (n + 1) q t epsilon) *
        Real.rpow (2 * epsilon) ((2 * s + (n : ℝ) / p) / 2) =
        Real.sqrt n * Real.rpow 2 ((2 * s + (n : ℝ) / p) / 2) *
          Real.rpow epsilon (-paramTheta (n + 1) p q s t) := by
      unfold polynomialParallel
      rw [hnR, Real.sqrt_mul hn0.le, op_sqrt_rpow he.le,
        show Real.rpow (2 * epsilon) ((2 * s + (n : ℝ) / p) / 2) =
          Real.rpow 2 ((2 * s + (n : ℝ) / p) / 2) *
            Real.rpow epsilon ((2 * s + (n : ℝ) / p) / 2) from
          Real.mul_rpow (by norm_num) he.le]
      have hexp : -paramTheta (n + 1) p q s t =
          (2 * polynomialHatT (n + 1) q t - 2) / 2 + (2 * s + (n : ℝ) / p) / 2 := by
        rw [hθeq, hy1]; ring
      have hadd : Real.rpow epsilon (-paramTheta (n + 1) p q s t) =
          Real.rpow epsilon ((2 * polynomialHatT (n + 1) q t - 2) / 2) *
            Real.rpow epsilon ((2 * s + (n : ℝ) / p) / 2) := by
        rw [hexp]; exact Real.rpow_add he _ _
      rw [hadd]; ring
    have e2 : Real.sqrt (polynomialPerpendicular (n + 1) q t epsilon)⁻¹ *
        Real.rpow (2 * epsilon) ((2 * t + (n : ℝ) / q) / 2) =
        Real.rpow 2 (polynomialHatT (n + 1) q t) := by
      unfold polynomialPerpendicular
      have hinv : (Real.rpow epsilon (2 * polynomialHatT (n + 1) q t))⁻¹ =
          Real.rpow epsilon (-(2 * polynomialHatT (n + 1) q t)) :=
        (Real.rpow_neg he.le _).symm
      rw [hinv, op_sqrt_rpow he.le, hy2,
        show Real.rpow (2 * epsilon) (polynomialHatT (n + 1) q t) =
          Real.rpow 2 (polynomialHatT (n + 1) q t) *
            Real.rpow epsilon (polynomialHatT (n + 1) q t) from
          Real.mul_rpow (by norm_num) he.le]
      have : Real.rpow epsilon (-(2 * polynomialHatT (n + 1) q t) / 2) *
          Real.rpow epsilon (polynomialHatT (n + 1) q t) = 1 := by
        calc _ = Real.rpow epsilon (-(2 * polynomialHatT (n + 1) q t) / 2 +
              polynomialHatT (n + 1) q t) := (Real.rpow_add he _ _).symm
          _ = 1 := by
            rw [show -(2 * polynomialHatT (n + 1) q t) / 2 + polynomialHatT (n + 1) q t = 0 by ring]
            exact Real.rpow_zero _
      calc _ = Real.rpow 2 (polynomialHatT (n + 1) q t) *
            (Real.rpow epsilon (-(2 * polynomialHatT (n + 1) q t) / 2) *
              Real.rpow epsilon (polynomialHatT (n + 1) q t)) := by ring
        _ = _ := by rw [this, mul_one]
    refine ⟨?_, ?_⟩
    · refine (hup ha).trans (le_of_eq ?_)
      congr 2
      rw [show (1 - Real.rpow 3 (-s)) * Real.sqrt (polynomialParallel (n + 1) q t epsilon) *
          (K1 * Real.rpow (2 * epsilon) ((2 * s + (n : ℝ) / p) / 2)) =
          (1 - Real.rpow 3 (-s)) * K1 * (Real.sqrt (polynomialParallel (n + 1) q t epsilon) *
            Real.rpow (2 * epsilon) ((2 * s + (n : ℝ) / p) / 2)) by ring, e1, hB1]
      ring
    · refine (hlo ha).trans (le_of_eq ?_)
      congr 2
      rw [show (1 - Real.rpow 3 (-t)) * Real.sqrt (polynomialPerpendicular (n + 1) q t epsilon)⁻¹ *
          (K2 * Real.rpow (2 * epsilon) ((2 * t + (n : ℝ) / q) / 2)) =
          (1 - Real.rpow 3 (-t)) * K2 * (Real.sqrt (polynomialPerpendicular (n + 1) q t epsilon)⁻¹ *
            Real.rpow (2 * epsilon) ((2 * t + (n : ℝ) / q) / 2)) by ring, e2, hB2]
      ring
  obtain ⟨hk1, hk2⟩ := key _ _ hfield
  have hC1 : (1 + B1) ^ 2 ≤ max 1 (max ((1 + B1) ^ 2) ((1 + B2) ^ 2)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC2 : (1 + B2) ^ 2 ≤ max 1 (max ((1 + B1) ^ 2) ((1 + B2) ^ 2)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hC0 : 0 < max 1 (max ((1 + B1) ^ 2) ((1 + B2) ^ 2)) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨hk1.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · set z := Real.rpow epsilon (-paramTheta (n + 1) p q s t)
    rw [← hz2]
    have h1 : 1 + B1 * z ≤ (1 + B1) * z := by nlinarith
    have h0 : 0 ≤ 1 + B1 * z := by positivity
    calc (1 + B1 * z) ^ 2 ≤ ((1 + B1) * z) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (1 + B1) ^ 2 * z ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 (by positivity)
  · have h3 : (lowerMoment (polynomialCoefficientFamily (n + 1) q t epsilon)
        (optimalPowers_family_weightedCoeffOn (n + 1) hd q t epsilon) t q ht hq.le)⁻¹ ≤
        ENNReal.ofReal (max 1 (max ((1 + B1) ^ 2) ((1 + B2) ^ 2))) :=
      hk2.trans (ENNReal.ofReal_le_ofReal hC2)
    rw [ENNReal.ofReal_inv_of_pos hC0]
    calc (ENNReal.ofReal (max 1 (max ((1 + B1) ^ 2) ((1 + B2) ^ 2))))⁻¹
        ≤ ((lowerMoment (polynomialCoefficientFamily (n + 1) q t epsilon)
        (optimalPowers_family_weightedCoeffOn (n + 1) hd q t epsilon) t q ht hq.le)⁻¹)⁻¹ :=
          ENNReal.inv_le_inv.2 h3
      _ = _ := inv_inv _

end

end CoarseDeGiorgi.SharpnessExamples
